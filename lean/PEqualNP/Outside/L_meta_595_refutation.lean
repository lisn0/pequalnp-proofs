import Mathlib
import PEqualNP.Defs

-- The finite search and its completeness proof are adapted from L_meta_516.

-- Adapted from Lewis Watson’s checked circuit analyses for L-meta-515 and L-meta-528.

namespace Live595

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

-- Any pair of rows which the output separates must stay separated at each cut.
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Live595

namespace Live595
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live595

namespace Check595

abbrev W := BitVec 384
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 192)).setWidth 192
def cuts (ws : List W) : BitVec 192 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 192) ++ (0 : BitVec 192)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 192) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x08bb8b011627c02b02b2232eb04037e1153eaad7bb7defbf000fff000003c000000001fff00001e0001c000000000000,
   0x1450c5228a485245b6505e42509d6a22f2e7337addfeb7df0000000000000000fff01e00003ffe00f0e0000000000000,
   0xb86106170c1c89660461e40463c04c47234bc39cee6f3beefff0001ffe1c0fff0001e00003c000070300000000000000,
   0x2182185731e10978978e00098101908ffc13fc1f0fb7c2f40000001fffe00ffffffe000000000007fc00000000000000,
   0xbb0bb0e4608001901904883107d7e1fc4803ffe00fc7fcf8ffffffe0000000000000000003fffff80000000000000000,
   0xc20c209841122de0de0fffbe0e2601100003fffff007ff000000000000000ffffffffffffc0000000000000000000000,
   0xfc0fc0ff81fffe00e00911c0083800008083fffffff80000fffffffffffff00000000000000000000000000000000000]

def inputs := rawInputs.map canon

end Check595
namespace Check595
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check595

namespace Check595
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 192) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (192+i.val)

theorem neg_differs (i : Fin 192) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 384 := by omega
  have hi : 192+i.val < 384 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 192) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 192) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (192+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (192+i.val) := by simpa [differs] using h.2
  have lo : i.val < 384 := by omega
  have hi : 192+i.val < 384 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 192) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬192 + i.val < 192 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 192) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live595.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live595.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 192)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check595

namespace Check595

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : Live595.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live595.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live595.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live595.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check595

namespace Check595
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 384) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 384) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 384 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 192) ++ (0 : BitVec 192))) :
    Live595.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 192) ++ (0 : BitVec 192)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 192) ++ (0 : BitVec 192)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 192) ++ (0 : BitVec 192)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1)

def assignment (k : Fin 384) (i : Fin 7) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live595.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 192) := [53, 50, 51, 52, 59, 68, 55]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (192+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live595.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 384) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 384) : graph (assignment k) =
    bit k ((-1 : BitVec 192) ++ (0 : BitVec 192)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 2 &&& x 1) ||| (x 0 &&& x 3) |||
    (x 3 &&& x 4) ||| (x 4 &&& x 5) ||| (x 5 &&& x 6) ||| (x 6 &&& x 1) =
      ((-1 : BitVec 192) ++ (0 : BitVec 192)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 384) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 192) ++ (0 : BitVec 192)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = graph x) :
    Live595.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live595.build basicOps goal k inputs.toFinset) :
    Live595.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live595.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live595.live basicOps goal m inputs.toFinset) :
    Live595.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem lower_of_check (check : search 10 inputs = false) (s : ℕ)
    (h : HasCircuitSize 7 graph s) : 11 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 10 := by change C.gates.length ≤ s at hsize; omega
  have searched := search_complete 10 inputs (by decide) (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check595
namespace Check595

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let z := canon w
    if z ∈ a :: b :: r then false
    else
      let v := sep w ||| base
      ((v == -1) && next extra (z :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (z :: a :: r)) ||
                         ((v ||| sep b == -1) && next (extra-1) (z :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (z :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) =>
      if k = 0 then (ops a b).any (· == goal) else dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hfresh : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp only [if_neg hfresh]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end Check595

namespace Check595

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live595.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live595.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      by_cases hk0 : k = 0
      · have hzgoal : z = goal := by
          subst k
          have hsingle : insert z needed = {goal} := tail
          have hmem : z ∈ insert z needed := Finset.mem_insert_self _ _
          rw [hsingle] at hmem
          exact Finset.mem_singleton.mp hmem
        subst z
        simp only [optimized, hk0, if_pos, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        right
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, goal, List.mem_toFinset.mp hz, rfl⟩
        · exact ⟨(b,a,r), swap, goal, List.mem_toFinset.mp (ops_swap a b ▸ hz), rfl⟩
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live595.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live595.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hfresh : z ∉ a :: b :: r := by
          intro hz'
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz'))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hfresh
          hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, if_neg hk0, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_optimized (check : optimized 10 4 inputs = false) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph s) : 11 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 10 := by change C.gates.length ≤ s at hsize; omega
  have searched := optimized_complete 10 inputs 4 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check595

namespace Check595

def gateBranch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W)
    (w : W) (branch : Fin 4) : Bool :=
  let z := canon w
  if z ∈ a :: b :: r then false
  else
    let v := sep w ||| cuts r
    match branch.val with
    | 0 => (v == -1) && next extra (z :: r)
      | 1 => (extra != 0) && ((v ||| sep a == -1) && next (extra-1) (z :: a :: r))
      | 2 => (extra != 0) && ((v ||| sep b == -1) && next (extra-1) (z :: b :: r))
    | _ => (extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (z :: a :: b :: r)

theorem dispatch_cases (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W)
    (h : dispatch extra next a b r = true) :
    ∃ w ∈ rawOps a b, ∃ branch : Fin 4, gateBranch extra next a b r w branch = true := by
  obtain ⟨w, hw, hok⟩ := List.any_eq_true.mp h
  refine ⟨w, hw, ?_⟩
  by_cases hdup : canon w ∈ a :: b :: r
  · simp [hdup] at hok
  · simp only [if_neg hdup, Bool.or_eq_true, Bool.and_eq_true] at hok
    rcases hok with (h0 | ⟨hmore, h1 | h2⟩) | h3
    · exact ⟨0, by simpa [gateBranch, hdup, Bool.and_eq_true] using h0⟩
      · refine ⟨1, ?_⟩
        simpa [gateBranch, hdup] using Bool.and_eq_true.mpr ⟨hmore, Bool.and_eq_true.mpr h1⟩
      · refine ⟨2, ?_⟩
        simpa [gateBranch, hdup] using Bool.and_eq_true.mpr ⟨hmore, Bool.and_eq_true.mpr h2⟩
    · exact ⟨3, by simpa [gateBranch, hdup, Bool.and_eq_true] using h3⟩

def branchCheck (i j : ℕ) (branch : Fin 4) : Bool :=
  ((pairs inputs)[i]?).any fun (a,b,r) =>
    ((rawOps a b)[j]?).any fun w => gateBranch 4 (optimized 9) a b r w branch

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_0 : branchCheck 0 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_1 : branchCheck 0 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_2 : branchCheck 0 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_3 : branchCheck 0 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_0 : branchCheck 0 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_1 : branchCheck 0 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_2 : branchCheck 0 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_3 : branchCheck 0 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_0 : branchCheck 0 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_1 : branchCheck 0 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_2 : branchCheck 0 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_3 : branchCheck 0 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_0 : branchCheck 0 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_1 : branchCheck 0 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_2 : branchCheck 0 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_3 : branchCheck 0 3 3 = false := by decide +kernel

private theorem checkedPair0 (j k : Fin 4) : branchCheck 0 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch0_0_0
  · exact branch0_0_1
  · exact branch0_0_2
  · exact branch0_0_3
  · exact branch0_1_0
  · exact branch0_1_1
  · exact branch0_1_2
  · exact branch0_1_3
  · exact branch0_2_0
  · exact branch0_2_1
  · exact branch0_2_2
  · exact branch0_2_3
  · exact branch0_3_0
  · exact branch0_3_1
  · exact branch0_3_2
  · exact branch0_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_0 : branchCheck 1 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_1 : branchCheck 1 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_2 : branchCheck 1 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_3 : branchCheck 1 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_0 : branchCheck 1 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_1 : branchCheck 1 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_2 : branchCheck 1 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_3 : branchCheck 1 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_0 : branchCheck 1 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_1 : branchCheck 1 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_2 : branchCheck 1 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_3 : branchCheck 1 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_0 : branchCheck 1 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_1 : branchCheck 1 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_2 : branchCheck 1 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_3 : branchCheck 1 3 3 = false := by decide +kernel

private theorem checkedPair1 (j k : Fin 4) : branchCheck 1 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch1_0_0
  · exact branch1_0_1
  · exact branch1_0_2
  · exact branch1_0_3
  · exact branch1_1_0
  · exact branch1_1_1
  · exact branch1_1_2
  · exact branch1_1_3
  · exact branch1_2_0
  · exact branch1_2_1
  · exact branch1_2_2
  · exact branch1_2_3
  · exact branch1_3_0
  · exact branch1_3_1
  · exact branch1_3_2
  · exact branch1_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_0 : branchCheck 2 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_1 : branchCheck 2 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_2 : branchCheck 2 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_3 : branchCheck 2 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_0 : branchCheck 2 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_1 : branchCheck 2 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_2 : branchCheck 2 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_3 : branchCheck 2 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_0 : branchCheck 2 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_1 : branchCheck 2 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_2 : branchCheck 2 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_3 : branchCheck 2 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_0 : branchCheck 2 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_1 : branchCheck 2 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_2 : branchCheck 2 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_3 : branchCheck 2 3 3 = false := by decide +kernel

private theorem checkedPair2 (j k : Fin 4) : branchCheck 2 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch2_0_0
  · exact branch2_0_1
  · exact branch2_0_2
  · exact branch2_0_3
  · exact branch2_1_0
  · exact branch2_1_1
  · exact branch2_1_2
  · exact branch2_1_3
  · exact branch2_2_0
  · exact branch2_2_1
  · exact branch2_2_2
  · exact branch2_2_3
  · exact branch2_3_0
  · exact branch2_3_1
  · exact branch2_3_2
  · exact branch2_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_0 : branchCheck 3 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_1 : branchCheck 3 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_2 : branchCheck 3 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_3 : branchCheck 3 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_0 : branchCheck 3 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_1 : branchCheck 3 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_2 : branchCheck 3 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_3 : branchCheck 3 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_0 : branchCheck 3 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_1 : branchCheck 3 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_2 : branchCheck 3 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_3 : branchCheck 3 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_0 : branchCheck 3 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_1 : branchCheck 3 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_2 : branchCheck 3 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_3 : branchCheck 3 3 3 = false := by decide +kernel

private theorem checkedPair3 (j k : Fin 4) : branchCheck 3 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch3_0_0
  · exact branch3_0_1
  · exact branch3_0_2
  · exact branch3_0_3
  · exact branch3_1_0
  · exact branch3_1_1
  · exact branch3_1_2
  · exact branch3_1_3
  · exact branch3_2_0
  · exact branch3_2_1
  · exact branch3_2_2
  · exact branch3_2_3
  · exact branch3_3_0
  · exact branch3_3_1
  · exact branch3_3_2
  · exact branch3_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_0 : branchCheck 4 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_1 : branchCheck 4 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_2 : branchCheck 4 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_3 : branchCheck 4 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_0 : branchCheck 4 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_1 : branchCheck 4 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_2 : branchCheck 4 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_3 : branchCheck 4 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_0 : branchCheck 4 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_1 : branchCheck 4 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_2 : branchCheck 4 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_3 : branchCheck 4 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_0 : branchCheck 4 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_1 : branchCheck 4 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_2 : branchCheck 4 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_3 : branchCheck 4 3 3 = false := by decide +kernel

private theorem checkedPair4 (j k : Fin 4) : branchCheck 4 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch4_0_0
  · exact branch4_0_1
  · exact branch4_0_2
  · exact branch4_0_3
  · exact branch4_1_0
  · exact branch4_1_1
  · exact branch4_1_2
  · exact branch4_1_3
  · exact branch4_2_0
  · exact branch4_2_1
  · exact branch4_2_2
  · exact branch4_2_3
  · exact branch4_3_0
  · exact branch4_3_1
  · exact branch4_3_2
  · exact branch4_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_0 : branchCheck 5 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_1 : branchCheck 5 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_2 : branchCheck 5 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_3 : branchCheck 5 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_0 : branchCheck 5 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_1 : branchCheck 5 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_2 : branchCheck 5 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_3 : branchCheck 5 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_0 : branchCheck 5 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_1 : branchCheck 5 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_2 : branchCheck 5 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_3 : branchCheck 5 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_0 : branchCheck 5 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_1 : branchCheck 5 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_2 : branchCheck 5 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_3 : branchCheck 5 3 3 = false := by decide +kernel

private theorem checkedPair5 (j k : Fin 4) : branchCheck 5 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch5_0_0
  · exact branch5_0_1
  · exact branch5_0_2
  · exact branch5_0_3
  · exact branch5_1_0
  · exact branch5_1_1
  · exact branch5_1_2
  · exact branch5_1_3
  · exact branch5_2_0
  · exact branch5_2_1
  · exact branch5_2_2
  · exact branch5_2_3
  · exact branch5_3_0
  · exact branch5_3_1
  · exact branch5_3_2
  · exact branch5_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_0 : branchCheck 6 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_1 : branchCheck 6 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_2 : branchCheck 6 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_3 : branchCheck 6 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_0 : branchCheck 6 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_1 : branchCheck 6 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_2 : branchCheck 6 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_3 : branchCheck 6 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_0 : branchCheck 6 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_1 : branchCheck 6 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_2 : branchCheck 6 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_3 : branchCheck 6 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_0 : branchCheck 6 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_1 : branchCheck 6 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_2 : branchCheck 6 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_3 : branchCheck 6 3 3 = false := by decide +kernel

private theorem checkedPair6 (j k : Fin 4) : branchCheck 6 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch6_0_0
  · exact branch6_0_1
  · exact branch6_0_2
  · exact branch6_0_3
  · exact branch6_1_0
  · exact branch6_1_1
  · exact branch6_1_2
  · exact branch6_1_3
  · exact branch6_2_0
  · exact branch6_2_1
  · exact branch6_2_2
  · exact branch6_2_3
  · exact branch6_3_0
  · exact branch6_3_1
  · exact branch6_3_2
  · exact branch6_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_0 : branchCheck 7 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_1 : branchCheck 7 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_2 : branchCheck 7 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_3 : branchCheck 7 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_0 : branchCheck 7 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_1 : branchCheck 7 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_2 : branchCheck 7 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_3 : branchCheck 7 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_0 : branchCheck 7 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_1 : branchCheck 7 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_2 : branchCheck 7 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_3 : branchCheck 7 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_0 : branchCheck 7 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_1 : branchCheck 7 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_2 : branchCheck 7 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_3 : branchCheck 7 3 3 = false := by decide +kernel

private theorem checkedPair7 (j k : Fin 4) : branchCheck 7 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch7_0_0
  · exact branch7_0_1
  · exact branch7_0_2
  · exact branch7_0_3
  · exact branch7_1_0
  · exact branch7_1_1
  · exact branch7_1_2
  · exact branch7_1_3
  · exact branch7_2_0
  · exact branch7_2_1
  · exact branch7_2_2
  · exact branch7_2_3
  · exact branch7_3_0
  · exact branch7_3_1
  · exact branch7_3_2
  · exact branch7_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_0 : branchCheck 8 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_1 : branchCheck 8 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_2 : branchCheck 8 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_3 : branchCheck 8 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_0 : branchCheck 8 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_1 : branchCheck 8 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_2 : branchCheck 8 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_3 : branchCheck 8 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_0 : branchCheck 8 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_1 : branchCheck 8 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_2 : branchCheck 8 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_3 : branchCheck 8 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_0 : branchCheck 8 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_1 : branchCheck 8 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_2 : branchCheck 8 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_3 : branchCheck 8 3 3 = false := by decide +kernel

private theorem checkedPair8 (j k : Fin 4) : branchCheck 8 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch8_0_0
  · exact branch8_0_1
  · exact branch8_0_2
  · exact branch8_0_3
  · exact branch8_1_0
  · exact branch8_1_1
  · exact branch8_1_2
  · exact branch8_1_3
  · exact branch8_2_0
  · exact branch8_2_1
  · exact branch8_2_2
  · exact branch8_2_3
  · exact branch8_3_0
  · exact branch8_3_1
  · exact branch8_3_2
  · exact branch8_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_0 : branchCheck 9 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_1 : branchCheck 9 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_2 : branchCheck 9 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_3 : branchCheck 9 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_0 : branchCheck 9 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_1 : branchCheck 9 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_2 : branchCheck 9 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_3 : branchCheck 9 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_0 : branchCheck 9 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_1 : branchCheck 9 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_2 : branchCheck 9 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_3 : branchCheck 9 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_0 : branchCheck 9 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_1 : branchCheck 9 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_2 : branchCheck 9 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_3 : branchCheck 9 3 3 = false := by decide +kernel

private theorem checkedPair9 (j k : Fin 4) : branchCheck 9 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch9_0_0
  · exact branch9_0_1
  · exact branch9_0_2
  · exact branch9_0_3
  · exact branch9_1_0
  · exact branch9_1_1
  · exact branch9_1_2
  · exact branch9_1_3
  · exact branch9_2_0
  · exact branch9_2_1
  · exact branch9_2_2
  · exact branch9_2_3
  · exact branch9_3_0
  · exact branch9_3_1
  · exact branch9_3_2
  · exact branch9_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_0 : branchCheck 10 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_1 : branchCheck 10 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_2 : branchCheck 10 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_3 : branchCheck 10 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_0 : branchCheck 10 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_1 : branchCheck 10 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_2 : branchCheck 10 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_3 : branchCheck 10 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_0 : branchCheck 10 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_1 : branchCheck 10 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_2 : branchCheck 10 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_3 : branchCheck 10 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_0 : branchCheck 10 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_1 : branchCheck 10 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_2 : branchCheck 10 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_3 : branchCheck 10 3 3 = false := by decide +kernel

private theorem checkedPair10 (j k : Fin 4) : branchCheck 10 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch10_0_0
  · exact branch10_0_1
  · exact branch10_0_2
  · exact branch10_0_3
  · exact branch10_1_0
  · exact branch10_1_1
  · exact branch10_1_2
  · exact branch10_1_3
  · exact branch10_2_0
  · exact branch10_2_1
  · exact branch10_2_2
  · exact branch10_2_3
  · exact branch10_3_0
  · exact branch10_3_1
  · exact branch10_3_2
  · exact branch10_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_0 : branchCheck 11 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_1 : branchCheck 11 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_2 : branchCheck 11 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_3 : branchCheck 11 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_0 : branchCheck 11 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_1 : branchCheck 11 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_2 : branchCheck 11 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_3 : branchCheck 11 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_0 : branchCheck 11 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_1 : branchCheck 11 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_2 : branchCheck 11 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_3 : branchCheck 11 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_0 : branchCheck 11 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_1 : branchCheck 11 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_2 : branchCheck 11 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_3 : branchCheck 11 3 3 = false := by decide +kernel

private theorem checkedPair11 (j k : Fin 4) : branchCheck 11 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch11_0_0
  · exact branch11_0_1
  · exact branch11_0_2
  · exact branch11_0_3
  · exact branch11_1_0
  · exact branch11_1_1
  · exact branch11_1_2
  · exact branch11_1_3
  · exact branch11_2_0
  · exact branch11_2_1
  · exact branch11_2_2
  · exact branch11_2_3
  · exact branch11_3_0
  · exact branch11_3_1
  · exact branch11_3_2
  · exact branch11_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_0 : branchCheck 12 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_1 : branchCheck 12 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_2 : branchCheck 12 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_3 : branchCheck 12 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_0 : branchCheck 12 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_1 : branchCheck 12 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_2 : branchCheck 12 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_3 : branchCheck 12 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_0 : branchCheck 12 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_1 : branchCheck 12 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_2 : branchCheck 12 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_3 : branchCheck 12 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_0 : branchCheck 12 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_1 : branchCheck 12 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_2 : branchCheck 12 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_3 : branchCheck 12 3 3 = false := by decide +kernel

private theorem checkedPair12 (j k : Fin 4) : branchCheck 12 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch12_0_0
  · exact branch12_0_1
  · exact branch12_0_2
  · exact branch12_0_3
  · exact branch12_1_0
  · exact branch12_1_1
  · exact branch12_1_2
  · exact branch12_1_3
  · exact branch12_2_0
  · exact branch12_2_1
  · exact branch12_2_2
  · exact branch12_2_3
  · exact branch12_3_0
  · exact branch12_3_1
  · exact branch12_3_2
  · exact branch12_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_0 : branchCheck 13 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_1 : branchCheck 13 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_2 : branchCheck 13 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_3 : branchCheck 13 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_0 : branchCheck 13 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_1 : branchCheck 13 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_2 : branchCheck 13 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_3 : branchCheck 13 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_0 : branchCheck 13 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_1 : branchCheck 13 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_2 : branchCheck 13 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_3 : branchCheck 13 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_0 : branchCheck 13 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_1 : branchCheck 13 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_2 : branchCheck 13 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_3 : branchCheck 13 3 3 = false := by decide +kernel

private theorem checkedPair13 (j k : Fin 4) : branchCheck 13 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch13_0_0
  · exact branch13_0_1
  · exact branch13_0_2
  · exact branch13_0_3
  · exact branch13_1_0
  · exact branch13_1_1
  · exact branch13_1_2
  · exact branch13_1_3
  · exact branch13_2_0
  · exact branch13_2_1
  · exact branch13_2_2
  · exact branch13_2_3
  · exact branch13_3_0
  · exact branch13_3_1
  · exact branch13_3_2
  · exact branch13_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_0 : branchCheck 14 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_1 : branchCheck 14 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_2 : branchCheck 14 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_3 : branchCheck 14 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_0 : branchCheck 14 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_1 : branchCheck 14 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_2 : branchCheck 14 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_3 : branchCheck 14 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_0 : branchCheck 14 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_1 : branchCheck 14 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_2 : branchCheck 14 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_3 : branchCheck 14 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_0 : branchCheck 14 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_1 : branchCheck 14 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_2 : branchCheck 14 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_3 : branchCheck 14 3 3 = false := by decide +kernel

private theorem checkedPair14 (j k : Fin 4) : branchCheck 14 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch14_0_0
  · exact branch14_0_1
  · exact branch14_0_2
  · exact branch14_0_3
  · exact branch14_1_0
  · exact branch14_1_1
  · exact branch14_1_2
  · exact branch14_1_3
  · exact branch14_2_0
  · exact branch14_2_1
  · exact branch14_2_2
  · exact branch14_2_3
  · exact branch14_3_0
  · exact branch14_3_1
  · exact branch14_3_2
  · exact branch14_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_0 : branchCheck 15 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_1 : branchCheck 15 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_2 : branchCheck 15 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_3 : branchCheck 15 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_0 : branchCheck 15 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_1 : branchCheck 15 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_2 : branchCheck 15 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_3 : branchCheck 15 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_0 : branchCheck 15 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_1 : branchCheck 15 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_2 : branchCheck 15 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_3 : branchCheck 15 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_0 : branchCheck 15 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_1 : branchCheck 15 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_2 : branchCheck 15 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_3 : branchCheck 15 3 3 = false := by decide +kernel

private theorem checkedPair15 (j k : Fin 4) : branchCheck 15 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch15_0_0
  · exact branch15_0_1
  · exact branch15_0_2
  · exact branch15_0_3
  · exact branch15_1_0
  · exact branch15_1_1
  · exact branch15_1_2
  · exact branch15_1_3
  · exact branch15_2_0
  · exact branch15_2_1
  · exact branch15_2_2
  · exact branch15_2_3
  · exact branch15_3_0
  · exact branch15_3_1
  · exact branch15_3_2
  · exact branch15_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_0 : branchCheck 16 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_1 : branchCheck 16 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_2 : branchCheck 16 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_3 : branchCheck 16 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_0 : branchCheck 16 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_1 : branchCheck 16 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_2 : branchCheck 16 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_3 : branchCheck 16 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_0 : branchCheck 16 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_1 : branchCheck 16 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_2 : branchCheck 16 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_3 : branchCheck 16 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_0 : branchCheck 16 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_1 : branchCheck 16 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_2 : branchCheck 16 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_3 : branchCheck 16 3 3 = false := by decide +kernel

private theorem checkedPair16 (j k : Fin 4) : branchCheck 16 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch16_0_0
  · exact branch16_0_1
  · exact branch16_0_2
  · exact branch16_0_3
  · exact branch16_1_0
  · exact branch16_1_1
  · exact branch16_1_2
  · exact branch16_1_3
  · exact branch16_2_0
  · exact branch16_2_1
  · exact branch16_2_2
  · exact branch16_2_3
  · exact branch16_3_0
  · exact branch16_3_1
  · exact branch16_3_2
  · exact branch16_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_0 : branchCheck 17 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_1 : branchCheck 17 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_2 : branchCheck 17 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_3 : branchCheck 17 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_0 : branchCheck 17 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_1 : branchCheck 17 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_2 : branchCheck 17 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_3 : branchCheck 17 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_0 : branchCheck 17 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_1 : branchCheck 17 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_2 : branchCheck 17 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_3 : branchCheck 17 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_0 : branchCheck 17 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_1 : branchCheck 17 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_2 : branchCheck 17 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_3 : branchCheck 17 3 3 = false := by decide +kernel

private theorem checkedPair17 (j k : Fin 4) : branchCheck 17 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch17_0_0
  · exact branch17_0_1
  · exact branch17_0_2
  · exact branch17_0_3
  · exact branch17_1_0
  · exact branch17_1_1
  · exact branch17_1_2
  · exact branch17_1_3
  · exact branch17_2_0
  · exact branch17_2_1
  · exact branch17_2_2
  · exact branch17_2_3
  · exact branch17_3_0
  · exact branch17_3_1
  · exact branch17_3_2
  · exact branch17_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_0 : branchCheck 18 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_1 : branchCheck 18 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_2 : branchCheck 18 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_3 : branchCheck 18 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_0 : branchCheck 18 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_1 : branchCheck 18 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_2 : branchCheck 18 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_3 : branchCheck 18 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_0 : branchCheck 18 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_1 : branchCheck 18 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_2 : branchCheck 18 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_3 : branchCheck 18 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_0 : branchCheck 18 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_1 : branchCheck 18 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_2 : branchCheck 18 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_3 : branchCheck 18 3 3 = false := by decide +kernel

private theorem checkedPair18 (j k : Fin 4) : branchCheck 18 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch18_0_0
  · exact branch18_0_1
  · exact branch18_0_2
  · exact branch18_0_3
  · exact branch18_1_0
  · exact branch18_1_1
  · exact branch18_1_2
  · exact branch18_1_3
  · exact branch18_2_0
  · exact branch18_2_1
  · exact branch18_2_2
  · exact branch18_2_3
  · exact branch18_3_0
  · exact branch18_3_1
  · exact branch18_3_2
  · exact branch18_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_0 : branchCheck 19 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_1 : branchCheck 19 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_2 : branchCheck 19 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_3 : branchCheck 19 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_0 : branchCheck 19 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_1 : branchCheck 19 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_2 : branchCheck 19 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_3 : branchCheck 19 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_0 : branchCheck 19 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_1 : branchCheck 19 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_2 : branchCheck 19 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_3 : branchCheck 19 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_0 : branchCheck 19 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_1 : branchCheck 19 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_2 : branchCheck 19 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_3 : branchCheck 19 3 3 = false := by decide +kernel

private theorem checkedPair19 (j k : Fin 4) : branchCheck 19 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch19_0_0
  · exact branch19_0_1
  · exact branch19_0_2
  · exact branch19_0_3
  · exact branch19_1_0
  · exact branch19_1_1
  · exact branch19_1_2
  · exact branch19_1_3
  · exact branch19_2_0
  · exact branch19_2_1
  · exact branch19_2_2
  · exact branch19_2_3
  · exact branch19_3_0
  · exact branch19_3_1
  · exact branch19_3_2
  · exact branch19_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_0 : branchCheck 20 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_1 : branchCheck 20 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_2 : branchCheck 20 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_3 : branchCheck 20 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_0 : branchCheck 20 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_1 : branchCheck 20 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_2 : branchCheck 20 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_3 : branchCheck 20 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_0 : branchCheck 20 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_1 : branchCheck 20 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_2 : branchCheck 20 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_3 : branchCheck 20 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_0 : branchCheck 20 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_1 : branchCheck 20 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_2 : branchCheck 20 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_3 : branchCheck 20 3 3 = false := by decide +kernel

private theorem checkedPair20 (j k : Fin 4) : branchCheck 20 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch20_0_0
  · exact branch20_0_1
  · exact branch20_0_2
  · exact branch20_0_3
  · exact branch20_1_0
  · exact branch20_1_1
  · exact branch20_1_2
  · exact branch20_1_3
  · exact branch20_2_0
  · exact branch20_2_1
  · exact branch20_2_2
  · exact branch20_2_3
  · exact branch20_3_0
  · exact branch20_3_1
  · exact branch20_3_2
  · exact branch20_3_3

private theorem checkedBranches (i : Fin 21) (j k : Fin 4) : branchCheck i.val j.val k = false := by
  fin_cases i
  · exact checkedPair0 j k
  · exact checkedPair1 j k
  · exact checkedPair2 j k
  · exact checkedPair3 j k
  · exact checkedPair4 j k
  · exact checkedPair5 j k
  · exact checkedPair6 j k
  · exact checkedPair7 j k
  · exact checkedPair8 j k
  · exact checkedPair9 j k
  · exact checkedPair10 j k
  · exact checkedPair11 j k
  · exact checkedPair12 j k
  · exact checkedPair13 j k
  · exact checkedPair14 j k
  · exact checkedPair15 j k
  · exact checkedPair16 j k
  · exact checkedPair17 j k
  · exact checkedPair18 j k
  · exact checkedPair19 j k
  · exact checkedPair20 j k

theorem verifiedSearch : optimized 10 4 inputs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [optimized, show ¬ (9 : ℕ) = 0 by decide, if_false, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with hstop | ⟨⟨a,b,r⟩, hp, hstep⟩
  · exact (by decide : (inputs == [goal]) ≠ true) hstop
  · obtain ⟨w, hw, branch, hbranch⟩ := dispatch_cases 4 (optimized 9) a b r hstep
    obtain ⟨i, hi⟩ := List.get_of_mem hp
    obtain ⟨j, hj⟩ := List.get_of_mem hw
    have hlen : (pairs inputs).length = 21 := by decide
    have hraw : (rawOps a b).length = 4 := by simp [rawOps]
    have hn := checkedBranches (Fin.cast hlen i) (Fin.cast hraw j) branch
    simp only [branchCheck, Fin.val_cast, List.getElem?_eq_getElem i.isLt, Option.any_some] at hn
    rw [hi] at hn
    simp only [List.getElem?_eq_getElem j.isLt, Option.any_some] at hn
    rw [hj] at hn
    exact Bool.noConfusion (hn.symm.trans hbranch)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem graphSpec (x : Fin 7 → Bool) : graph x = true ↔
    ∃ u v : Fin 7,
      (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true := by
  have check : ∀ x : Fin 7 → Bool, graph x = true ↔
      ∃ u v : Fin 7,
        (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true := by decide +kernel
  exact check x

end Check595

theorem PEqualNP.Outside.L_meta_595_refutation :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 7, (u.val, v.val) ∈
          ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true))) := by
  intro ⟨C, hOk, hSize, he⟩
  have hEval : ∀ x, C.eval (List.ofFn x) = Check595.graph x := by
    intro x
    exact Bool.eq_iff_iff.mpr ((he x).trans (Check595.graphSpec x).symm)
  have lower := Check595.lower_of_optimized Check595.verifiedSearch 10 ⟨C, hOk, hSize, hEval⟩
  omega
