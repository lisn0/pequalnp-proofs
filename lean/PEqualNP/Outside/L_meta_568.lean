import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation adapted from MetaComplexity/Helpers/Elim.lean.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht, List.append_assoc]
    rfl

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨tail, h, hlen⟩ := wiresFrom_prefix gs w
  simp [h, hlen]

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- A NOT gate reads only its first wire: drop the others. -/
private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
private abbrev Stat := Sum Bool ℕ

private def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
    next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

private theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
    saved. -/
private theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
    and every old wire has a valid status whose value on the new wires is the old value. -/
private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
    input is the constant `b`. -/
private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

private theorem normGate_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) : normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [normGate]

private theorem normGate_read (g : Gate) (n : ℕ)
    (h : g.op = GateOp.not ∧ g.inputs.head? = some n ∨
      g.op ≠ GateOp.not ∧ n ∈ g.inputs) : n ∈ (normGate g).inputs := by
  rcases h with ⟨hop, hhead⟩ | ⟨hop, hmem⟩
  · have htake : g.inputs.take 1 = [n] := by
      rcases h : g.inputs with _ | ⟨a, ins⟩ <;> simp_all
    simp [normGate, hop, htake]
  · simpa only [normGate_of_ne_not g hop] using hmem

private theorem elim_stat_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem elim_read_const (n k : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (hread : k ∈ g.inputs) (b : Bool)
    (hfix : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
    simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
      (fun h => by simpa using hg.2 h) ⟨b, List.mem_map.mpr ⟨k, hread, hfix⟩⟩
  change (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]
  simp

private theorem bad_reader_constant (n m : ℕ) (stats : List Stat) (g : Gate)
    (hg : NOk g) (hread : n ∈ g.inputs) (hfix : stats.getD n (Sum.inl false) = Sum.inl false)
    (hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < stats.length)) :
    ∃ b, (simplify g.op m (g.inputs.map fun i => stats.getD i (Sum.inl false))).2 =
      Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1.1
  have hlen : ins.length ≤ 2 := hg.1.2
  simp only [List.getD_eq_getElem?_getD] at hfix
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpAnd, hfix]⟩
    · have hmem : n = a ∨ n = b := by simpa using hread
      rcases hmem with ha | hb
      · subst a
        refine ⟨false, ?_⟩
        cases hb : stats[b]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, hb]
      · subst b
        refine ⟨false, ?_⟩
        cases ha : stats[a]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, ha]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpOr, hfix]⟩
    · have hout (w : ℕ) (hw : w ∈ [a, b]) :
          stats[w]?.getD (Sum.inl false) = Sum.inl false := by
        by_cases hn : w = n
        · simpa only [hn] using hfix
        · have hnlt : ¬w < stats.length := fun hlt => hbad ⟨rfl, rfl, w, hw, hn, hlt⟩
          exact List.getD_eq_default _ _ (Nat.le_of_not_gt hnlt)
      exact ⟨false, by simp [simplify, simpOr, hout a (by simp), hout b (by simp)]⟩
    · simp at hlen
  · have hone : ins.length ≤ 1 := hg.2 rfl
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨true, by simp [simplify, simpNot, hfix]⟩
    · simp at hone

private theorem wires_agree (gs : List Gate) (bad : ℕ → Prop) (w w' : List Bool)
    (hlen : w.length = w'.length)
    (hw : ∀ i, ¬bad i → w.getD i false = w'.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬bad i) :
    ∀ i, ¬bad i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact hw
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hv : v = v' := by
      dsimp only [v, v']
      congr 1
      exact List.map_congr_left (fun i hi => hw i (hgs g List.mem_cons_self i hi))
    change ∀ i, ¬bad i → (wiresFrom gs (w ++ [v])).getD i false =
      (wiresFrom gs (w' ++ [v'])).getD i false
    apply ih _ _ (by simp [hlen]) _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i hi
    by_cases heq : i = w.length
    · rw [getD_snoc_len _ _ _ _ heq.symm, getD_snoc_len _ _ _ _ (hlen.symm.trans heq.symm), hv]
    · rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

private def reads (C : Circuit) (a : ℕ) (j : Fin C.gates.length) : Prop :=
  ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a) ∨
    ((C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs)

private theorem reads_norm_iff (C : Circuit) (a : ℕ) (j : Fin C.gates.length) :
    reads C a j ↔ a ∈ (normGate (C.gates.get j)).inputs := by
  unfold reads
  generalize C.gates.get j = g
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    cases inputs <;> simp [normGate, eq_comm]
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]

private def cutVal (n : ℕ) (C : Circuit) (a : ℕ) (b : Bool) (x : Fin (n + 1) → Bool) : Bool :=
  let gs := C.gates.map normGate
  let w := wiresFrom (gs.take (a - n)) (List.ofFn x)
  (wiresFrom (gs.drop (a - n)) (w.set a b)).getD C.output false


private theorem normed_ok (C : Circuit) (hc : FanInTwo C) :
    ∀ g ∈ C.gates.map normGate, NOk g := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact normGate_nok g' (hc g' hg')

private theorem normed_split (C : Circuit) (j : Fin C.gates.length) :
    C.gates.map normGate = (C.gates.map normGate).take j.val ++
      normGate (C.gates.get j) :: (C.gates.map normGate).drop (j.val + 1) := by
  have hj : j.val < (C.gates.map normGate).length := by simp
  have hs := List.take_append_drop j.val (C.gates.map normGate)
  rw [List.drop_eq_getElem_cons hj] at hs
  simpa [List.get_eq_getElem] using hs.symm

private def identityStats (m : ℕ) : List Stat :=
  List.ofFn (fun i : Fin m => Sum.inr (i : ℕ))

private theorem inv_identity (m : ℕ) (y : List Bool) (hy : y.length = m) (gs : List Gate) :
    Inv m y (wiresFrom gs y) (identityStats (m + gs.length), gs) := by
  refine ⟨by simp [identityStats, length_wiresFrom, hy], ?_⟩
  intro i
  let k := m + gs.length
  have hlen : (wiresFrom gs y).length = k := by simp [k, length_wiresFrom, hy]
  change ((identityStats k).getD i (Sum.inl false)).Valid k ∧
    ((identityStats k).getD i (Sum.inl false)).val (wiresFrom gs y) =
      (wiresFrom gs y).getD i false
  by_cases hi : i < k
  · have hget : (identityStats k).getD i (Sum.inl false) = Sum.inr i := by
      simp [identityStats, hi]
    rw [hget]
    exact ⟨hi, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [identityStats]; omega),
      List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial, rfl⟩

private theorem inv_skip (m : ℕ) (y : List Bool) (hy : y.length = m) (gs : List Gate) :
    Inv m y (wiresFrom gs y ++ [false]) (identityStats (m + gs.length) ++ [Sum.inl false], gs) := by
  have hv := inv_identity m y hy gs
  obtain ⟨hlen, hval⟩ := hv
  change (identityStats (m + gs.length)).length = (wiresFrom gs y).length at hlen
  refine ⟨by simp [hlen], ?_⟩
  intro i
  change (((identityStats (m + gs.length)) ++ [Sum.inl false]).getD i (Sum.inl false)).Valid
      (m + gs.length) ∧
    (((identityStats (m + gs.length)) ++ [Sum.inl false]).getD i (Sum.inl false)).val
      (wiresFrom gs y) = (wiresFrom gs y ++ [false]).getD i false
  by_cases hi : i = (wiresFrom gs y).length
  · rw [getD_snoc_len _ _ _ _ (hlen.trans hi.symm), getD_snoc_len _ _ _ _ hi.symm]
    exact ⟨trivial, rfl⟩
  · rw [getD_snoc_ne _ _ _ _ (by rwa [hlen]), getD_snoc_ne _ _ _ _ hi]
    exact hval i

private theorem minimal_of_status (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y, circuitFun m C x ≠ circuitFun m C y)
    (acc : List Stat × List Gate) (hok : ∀ g ∈ acc.2, Ok g)
    (hev : ∀ x : Fin m → Bool, (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn x)) = circuitFun m C x) :
    C.gates.length ≤ acc.2.length := by
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hne⟩ := hnc
    have hx := hev x
    have hy := hev y
    rw [hs] at hx hy
    exact (hne (hx.symm.trans hy)).elim
  | inr out =>
    apply hmin.2 (⟨acc.2, out⟩ : Circuit) hok
    funext x
    have hx := hev x
    rw [hs] at hx
    exact hx

private theorem cleanReads (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ x y, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y) :
    ∀ a j, reads C a j → a < n + 1 + j.val := by
  intro a j hr
  by_contra ha
  let m := n + 1
  let gs := C.gates.map normGate
  let pre := gs.take j.val
  let g := normGate (C.gates.get j)
  let post := gs.drop (j.val + 1)
  let start : List Stat × List Gate := (identityStats m, [])
  let before := elim m pre start
  let after := elimStep m before g
  let final := elim m post after
  have hsplit : gs = pre ++ g :: post := normed_split C j
  have hpreLen : pre.length = j.val := by
    simp [pre, gs, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hlen : gs.length = pre.length + 1 + post.length := by
    have hh := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons] at hh
    omega
  have hsize : C.gates.length = gs.length := by simp [gs]
  have hok : ∀ k ∈ gs, NOk k := normed_ok C hmin.1
  have hg : NOk g := hok g (by rw [hsplit]; simp)
  have hbefore : before.1.length = m + j.val := by
    rw [elim_stat_length]
    simp [start, identityStats, hpreLen]
  have hfix : before.1.getD a (Sum.inl false) = Sum.inl false :=
    List.getD_eq_default _ _ (by rw [hbefore]; exact Nat.le_of_not_gt ha)
  have hsave : after.2.length = before.2.length :=
    elim_read_const m a before g hg ((reads_norm_iff C a j).mp hr) false hfix
  have hfinal : elim m gs start = final := by
    rw [hsplit]
    simp only [elim, List.foldl_append]
    rfl
  have hfinalOk : ∀ k ∈ final.2, Ok k := by
    rw [← hfinal]
    exact elim_ok m gs start (by simp [start])
  have hfinalEval (x : Fin m → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) =
        circuitFun m C x := by
    have hstart : Inv m (List.ofFn x) (List.ofFn x) start := by
      simpa [start, wiresFrom] using inv_identity m (List.ofFn x) (by simp) []
    have he := ((inv_elim m (List.ofFn x) (by simp) gs _ start
      (fun k hk => (hok k hk).1) hstart).2 C.output).2
    rw [hfinal, wiresFrom_norm C.gates] at he
    exact he
  have hlo := minimal_of_status m C hmin hnc final hfinalOk hfinalEval
  have hbeforeLen : before.2.length ≤ pre.length := by
    simpa [before, start] using elim_len m pre start
  have hfinalLen : final.2.length ≤ after.2.length + post.length := elim_len m post after
  omega

private theorem liveGate (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ x y, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y)
    (j : Fin C.gates.length) (hne : n + 1 + j.val ≠ C.output) :
    ∃ k : Fin C.gates.length, j.val < k.val ∧ reads C (n + 1 + j.val) k := by
  by_contra hnone
  let m := n + 1
  let gs := C.gates.map normGate
  let pre := gs.take j.val
  let g := normGate (C.gates.get j)
  let post := gs.drop (j.val + 1)
  let start : List Stat × List Gate := (identityStats (m + pre.length) ++ [Sum.inl false], pre)
  let final := elim m post start
  have hsplit : gs = pre ++ g :: post := normed_split C j
  have hpreLen : pre.length = j.val := by
    simp [pre, gs, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hlen : C.gates.length = pre.length + 1 + post.length := by
    have hh := congrArg List.length hsplit
    simp only [gs, List.length_map, List.length_append, List.length_cons] at hh
    omega
  have hok : ∀ k ∈ gs, NOk k := normed_ok C hmin.1
  have hpostOk : ∀ k ∈ post, Ok k := by
    intro k hk
    exact (hok k (List.mem_of_mem_drop hk)).1
  have hpreOk : ∀ k ∈ start.2, Ok k := by
    intro k hk
    exact (hok k (List.mem_of_mem_take hk)).1
  have hpostNo (k : Gate) (hk : k ∈ post) (i : ℕ) (hi : i ∈ k.inputs) :
      i ≠ m + j.val := by
    intro he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hk
    have ht' : j.val + 1 + t < C.gates.length := by
      simp only [post, gs, List.length_drop, List.length_map] at ht
      omega
    let q : Fin C.gates.length := ⟨j.val + 1 + t, ht'⟩
    have hread : m + j.val ∈ (normGate (C.gates.get q)).inputs := by
      simpa only [he, post, gs, List.getElem_drop, List.getElem_map, List.get_eq_getElem, q] using hi
    exact hnone ⟨q, by dsimp [q]; omega, (reads_norm_iff C _ q).mpr hread⟩
  have hfinalEval (x : Fin m → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) =
        circuitFun m C x := by
    let w := wiresFrom pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hw : w.length = m + j.val := by simp [w, length_wiresFrom, hpreLen]
    have hne' : C.output ≠ m + j.val := Ne.symm hne
    have hagree := wires_agree post (fun i => i = m + j.val) (w ++ [false]) (w ++ [b])
      (by simp) (by
        intro i hi
        rw [getD_snoc_ne _ _ _ _ (by rwa [hw]), getD_snoc_ne _ _ _ _ (by rwa [hw])])
      hpostNo C.output hne'
    have hstart : Inv m (List.ofFn x) (w ++ [false]) start :=
      inv_skip m (List.ofFn x) (by simp) pre
    have he := ((inv_elim m (List.ofFn x) (by simp) post _ start hpostOk hstart).2 C.output).2
    change _ = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [← wiresFrom_norm C.gates, hsplit, wiresFrom_append]
    exact he.trans hagree
  have hlo := minimal_of_status m C hmin hnc final (elim_ok m post start hpreOk) hfinalEval
  have hfinalLen : final.2.length ≤ pre.length + post.length := elim_len m post start
  omega

private theorem outputLast (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ x y, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y)
    (hout : n < C.output) : C.output = n + C.gates.length := by
  have hlt : C.output < n + 1 + C.gates.length := by
    by_contra h
    have hc (x : Fin (n + 1) → Bool) : circuitFun (n + 1) C x = false := by
      change (wiresFrom C.gates (List.ofFn x)).getD C.output false = false
      apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
      omega
    obtain ⟨x, y, hne⟩ := hnc
    exact hne ((hc x).trans (hc y).symm)
  let k := C.output - n
  have hk : k ≤ C.gates.length := by dsimp [k]; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have hd : FanInTwo D := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
  have he : circuitFun (n + 1) D = circuitFun (n + 1) C := by
    funext x
    let w := wiresFrom (C.gates.take k) (List.ofFn x)
    have hw : C.output < w.length := by
      simp only [w, length_wiresFrom, List.length_ofFn, List.length_take, Nat.min_eq_left hk, k]
      omega
    change w.getD C.output false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    conv_rhs => rw [← List.take_append_drop k C.gates, wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix (C.gates.drop k) w
    change w.getD C.output false = (wiresFrom (C.gates.drop k) w).getD C.output false
    rw [ht, List.getD_append _ _ _ _ hw]
  have hlow := hmin.2 D hd he
  change C.gates.length ≤ (C.gates.take k).length at hlow
  rw [List.length_take, Nat.min_eq_left hk] at hlow
  dsimp [k] at hk hlow
  omega
private def cutStats (a : ℕ) : List Stat :=
  List.ofFn fun i : Fin (a + 1) => if i.val = a then Sum.inl false else Sum.inr i.val

private theorem cutStats_getD (a i : ℕ) (hi : i < a + 1) :
    (cutStats a).getD i (Sum.inl false) =
      if i = a then Sum.inl false else Sum.inr i := by
  unfold cutStats
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem cut_inv (n a : ℕ) (pre : List Gate) (x : Fin (n + 1) → Bool)
    (hlen : n + 1 + pre.length = a + 1) :
    Inv (n + 1) (List.ofFn x) ((wiresFrom pre (List.ofFn x)).set a false) (cutStats a, pre) := by
  have hw : (wiresFrom pre (List.ofFn x)).length = a + 1 := by
    simpa [length_wiresFrom] using hlen
  refine ⟨by simp [cutStats, hw], ?_⟩
  intro i
  by_cases hi : i < a + 1
  · change ((cutStats a).getD i (Sum.inl false)).Valid (n + 1 + pre.length) ∧ _
    rw [cutStats_getD a i hi]
    by_cases he : i = a
    · subst i
      simp [Stat.Valid, Stat.val, List.getD_eq_getElem?_getD, hw]
    · simp [he, Stat.Valid, Stat.val, List.getD_eq_getElem?_getD, hlen, hi]
  · change ((cutStats a).getD i (Sum.inl false)).Valid (n + 1 + pre.length) ∧ _
    rw [List.getD_eq_default _ _ (by simpa [cutStats] using Nat.le_of_not_gt hi)]
    have hout : ((wiresFrom pre (List.ofFn x)).set a false).length ≤ i := by
      simpa [hw] using Nat.le_of_not_gt hi
    rw [List.getD_eq_default _ _ hout]
    exact ⟨trivial, rfl⟩

private theorem cut_set_self (w : List Bool) (a : ℕ) :
    w.set a (w.getD a false) = w := by
  induction w generalizing a with
  | nil => cases a <;> rfl
  | cons b w ih =>
    cases a with
    | zero => rfl
    | succ a =>
      change b :: w.set a (w.getD a false) = b :: w
      rw [ih]

private theorem cut_elim_prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ t, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    change ∃ t, (elim n gs (elimStep n acc g)).2 = acc.2 ++ t
    rw [ht]
    simp only [elimStep, List.append_assoc]
    exact ⟨_, rfl⟩

private theorem cutStep (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hclean : ∀ j : Fin C.gates.length, ∀ i ∈ (normGate (C.gates.get j)).inputs,
      i < n + 1 + j.val)
    (hlive : ∀ j : Fin C.gates.length, n + 1 + j.val ≠ C.output →
      ∃ k : Fin C.gates.length, reads C (n + 1 + j.val) k)
    (hnonconst : ∃ x y : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y)
    (a : ℕ) (ha0 : n ≤ a) (ha1 : a ≤ n + C.gates.length) (_hao : a ≠ C.output)
    (ht : ∀ x, cutVal n C a true x = true) (j : Fin C.gates.length) (hj : reads C a j) :
    ((C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
      a ∈ (C.gates.get j).inputs ∧
      ∃ w ∈ (C.gates.get j).inputs, w ≠ a ∧ w < n + 1 + j.val) ∧
    (∀ k : Fin C.gates.length, reads C a k → k = j) := by
  classical
  let N := n + 1
  let gs := C.gates.map normGate
  let p := a - n
  let pre := gs.take p
  let rest := gs.drop p
  let g := normGate (C.gates.get j)
  let mid := rest.take (j.val - p)
  let post := rest.drop (j.val - p + 1)
  let start : List Stat × List Gate := (cutStats a, pre)
  let before := elim N mid start
  let after := elimStep N before g
  let final := elim N rest start
  let m := N + j.val
  have hgslen : gs.length = C.gates.length := by simp [gs]
  have hp : p ≤ gs.length := by dsimp [p]; omega
  have hplen : pre.length = p := by simp [pre, Nat.min_eq_left hp]
  have haLen : N + pre.length = a + 1 := by rw [hplen]; dsimp [N, p]; omega
  have hrestLen : rest.length = gs.length - p := by simp [rest]
  have hpk (k : Fin C.gates.length) (hk : reads C a k) : p ≤ k.val := by
    have hlt := hclean k a ((reads_norm_iff C a k).1 hk)
    dsimp [p]
    omega
  have hrestIdx (k : Fin C.gates.length) (hk : p ≤ k.val) :
      k.val - p < rest.length := by
    have hklt := k.isLt
    omega
  have hrestGet (k : Fin C.gates.length) (hk : p ≤ k.val) :
      rest[k.val - p]'(hrestIdx k hk) = normGate (C.gates.get k) := by
    have heq : p + (k.val - p) = k.val := by omega
    simp [rest, gs, List.getElem_drop, heq, List.get_eq_getElem]
  have hpj := hpk j hj
  have hjidx := hrestIdx j hpj
  have hsplit : rest = mid ++ g :: post := by
    have he := List.take_append_drop (j.val - p) rest
    rw [List.drop_eq_getElem_cons hjidx, hrestGet j hpj] at he
    exact he.symm
  have hmidlen : mid.length = j.val - p := by
    simp [mid, Nat.min_eq_left (Nat.le_of_lt hjidx)]
  have hsize : C.gates.length = pre.length + mid.length + 1 + post.length := by
    have he := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons] at he
    omega
  have hwhole : pre ++ rest = gs := List.take_append_drop p gs
  have hfinal : final = elim N post after := by
    change elim N rest start = _
    rw [hsplit]
    simp only [elim, List.foldl_append] <;> rfl
  have hok : ∀ k ∈ gs, NOk k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact normGate_nok _ (hmin.1 _ hk')
  have hokPre : ∀ k ∈ pre, NOk k := by
    intro k hk
    exact hok k (by rw [← hwhole]; exact List.mem_append_left _ hk)
  have hokRest : ∀ k ∈ rest, NOk k := by
    intro k hk
    exact hok k (by rw [← hwhole]; exact List.mem_append_right _ hk)
  have hg : NOk g := hokRest g (by rw [hsplit]; simp)
  have hokMid : ∀ k ∈ mid, NOk k := by
    intro k hk
    exact hokRest k (by rw [hsplit]; exact List.mem_append_left _ hk)
  have hokPost : ∀ k ∈ post, NOk k := by
    intro k hk
    exact hokRest k (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
  have hread : a ∈ g.inputs := (reads_norm_iff C a j).1 hj
  have hstartLen : start.1.length = a + 1 := by simp [start, cutStats]
  have hstartFix : start.1.getD a (Sum.inl false) = Sum.inl false := by
    change (cutStats a).getD a (Sum.inl false) = _
    simp [cutStats_getD a a (by omega)]
  have hm : before.1.length = m := by
    change (elim N mid start).1.length = m
    rw [elim_stat_length, hstartLen, hmidlen]
    change a + 1 + (j.val - (a - n)) = n + 1 + j.val
    change a - n ≤ j.val at hpj
    omega
  have ham : a < m := hclean j a hread
  have hbefore : before.1.getD a (Sum.inl false) = Sum.inl false :=
    (elim_getD N a _ mid start (by omega)).trans hstartFix
  have hsaved : after.2.length = before.2.length :=
    elim_read_const N a before g hg hread false hbefore
  have hafterLen : after.1.length = m + 1 := by simp [after, elimStep, hm]
  have hafterFix : after.1.getD a (Sum.inl false) = Sum.inl false := by
    change (before.1 ++ [_]).getD a (Sum.inl false) = _
    rw [getD_snoc_ne _ _ _ _ (by omega), hbefore]
  have hbeforeBound : before.2.length ≤ pre.length + mid.length := elim_len N mid start
  have hfinalBound : final.2.length ≤ after.2.length + post.length := by
    rw [hfinal]
    exact elim_len N post after
  have hval (x : Fin (n + 1) → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) =
        cutVal n C a false x := by
    have hv := inv_elim N (List.ofFn x) (by simp [N]) rest _ start
      (fun k hk => (hokRest k hk).1) (cut_inv n a pre x haLen)
    exact (hv.2 C.output).2
  have horiginal (x : Fin (n + 1) → Bool) :
      circuitFun (n + 1) C x =
        ((wiresFrom pre (List.ofFn x)).getD a false || cutVal n C a false x) := by
    let w := wiresFrom pre (List.ofFn x)
    have horig : circuitFun (n + 1) C x = cutVal n C a (w.getD a false) x := by
      change (wiresFrom C.gates (List.ofFn x)).getD C.output false =
        (wiresFrom rest (w.set a (w.getD a false))).getD C.output false
      rw [cut_set_self, ← wiresFrom_norm C.gates]
      change (wiresFrom gs (List.ofFn x)).getD C.output false = _
      rw [← hwhole, wiresFrom_append]
    change circuitFun (n + 1) C x = (w.getD a false || cutVal n C a false x)
    rw [horig]
    cases h : w.getD a false with
    | false => simp
    | true => simpa using ht x
  have hfinalOk : ∀ k ∈ final.2, Ok k :=
    elim_ok N rest start (fun k hk => (hokPre k hk).1)
  obtain ⟨out, hout⟩ : ∃ out, final.1.getD C.output (Sum.inl false) = Sum.inr out := by
    cases h : final.1.getD C.output (Sum.inl false) with
    | inr out => exact ⟨out, rfl⟩
    | inl b =>
      have hconst (x : Fin (n + 1) → Bool) : cutVal n C a false x = b := by
        simpa [h, Stat.val] using (hval x).symm
      cases b with
      | false =>
        have hsm := hmin.2 (⟨pre, a⟩ : Circuit) (fun k hk => (hokPre k hk).1) (by
          funext x
          change (wiresFrom pre (List.ofFn x)).getD a false = circuitFun (n + 1) C x
          simpa [hconst x] using (horiginal x).symm)
        change C.gates.length ≤ pre.length at hsm
        omega
      | true =>
        obtain ⟨x, y, hxy⟩ := hnonconst
        exfalso
        apply hxy
        rw [horiginal x, horiginal y, hconst x, hconst y]
        simp
  have hkeep (x : Fin (n + 1) → Bool) :
      (wiresFrom final.2 (List.ofFn x)).getD a false = (wiresFrom pre (List.ofFn x)).getD a false := by
    obtain ⟨t, ht⟩ := cut_elim_prefix N rest start
    change final.2 = pre ++ t at ht
    rw [ht, wiresFrom_append]
    obtain ⟨u, hu, _⟩ := wiresFrom_prefix t (wiresFrom pre (List.ofFn x))
    rw [hu, List.getD_append _ _ _ _ (by simp [length_wiresFrom, haLen])]
  have hretainedSize : C.gates.length ≤ final.2.length + 1 := by
    let gor : Gate := ⟨GateOp.or, [a, out]⟩
    let D : Circuit := ⟨final.2 ++ [gor], N + final.2.length⟩
    have hf : FanInTwo D := by
      intro k hk
      change k ∈ final.2 ++ [gor] at hk
      rcases List.mem_append.1 hk with hk | hk
      · exact hfinalOk k hk
      · simp only [List.mem_singleton] at hk
        subst k
        simp [Ok, gor]
    have hEq : circuitFun (n + 1) D = circuitFun (n + 1) C := by
      funext x
      rw [horiginal x]
      let w := wiresFrom final.2 (List.ofFn x)
      have hw : w.length = N + final.2.length := by simp [w, length_wiresFrom, N]
      have houtval := hval x
      rw [hout] at houtval
      change w.getD out false = cutVal n C a false x at houtval
      change (wiresFrom (final.2 ++ [gor]) (List.ofFn x)).getD
        (N + final.2.length) false = _
      rw [wiresFrom_append]
      change (w ++ [gor.op.eval (gor.inputs.map fun i => w.getD i false)]).getD
        (N + final.2.length) false = _
      rw [getD_snoc_len _ _ _ _ hw]
      change (w.getD a false || (w.getD out false || false)) = _
      rw [Bool.or_false, houtval]
      exact congrArg (fun b : Bool => b || cutVal n C a false x) (hkeep x)
    simpa [D, Circuit.size] using hmin.2 D hf hEq
  have hpostMem (k : Fin C.gates.length) (hjk : j.val < k.val) :
      normGate (C.gates.get k) ∈ post := by
    have hpk' : p ≤ k.val := by omega
    have hi : k.val - (j.val + 1) < post.length := by
      have h := hrestIdx k hpk'
      simp only [post, List.length_drop]
      omega
    have heq : j.val - p + 1 + (k.val - (j.val + 1)) = k.val - p := by omega
    have hget : post[k.val - (j.val + 1)] = normGate (C.gates.get k) := by
      change (rest.drop (j.val - p + 1))[k.val - (j.val + 1)] = _
      rw [List.getElem_drop]
      simpa only [heq] using hrestGet k hpk'
    exact hget ▸ List.getElem_mem hi
  refine ⟨?_, ?_⟩
  · by_contra hshape
    have hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
        ∃ w ∈ g.inputs, w ≠ a ∧ w < before.1.length) := by
      intro ⟨hop, hlen, w, hw, hne, hlt⟩
      have hop' : (C.gates.get j).op = GateOp.or := (normGate_op _).symm.trans hop
      have hgn : g = C.gates.get j := normGate_of_ne_not _ (by rw [hop']; simp)
      rw [hgn] at hlen hw
      exact hshape ⟨hop', hlen, by simpa only [hgn] using hread, w, hw, hne,
        by simpa [hm, m, N] using hlt⟩
    obtain ⟨b, hb⟩ := bad_reader_constant a (N + before.2.length) before.1 g hg hread
      hbefore hbad
    have hafterConst : after.1.getD m (Sum.inl false) = Sum.inl b := by
      change (before.1 ++ [_]).getD m (Sum.inl false) = _
      rw [getD_snoc_len _ _ _ _ hm, hb]
    have hneout : m ≠ C.output := by
      intro heq
      rw [← heq, hfinal,
        elim_getD N m _ post after (by omega), hafterConst] at hout
      cases hout
    obtain ⟨k, hk⟩ := hlive j hneout
    have hmk := (reads_norm_iff C m k).1 hk
    have hjk : j.val < k.val := by have := hclean k m hmk; dsimp [m] at this; omega
    have hpostSaved := elim_len_lt N m post after hokPost
      (by omega) ⟨b, hafterConst⟩ ⟨_, hpostMem k hjk, hmk⟩
    rw [← hfinal] at hpostSaved
    omega
  · intro k hk
    by_contra hkj
    have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    have hkr := (reads_norm_iff C a k).1 hk
    rcases lt_or_gt_of_ne hne with hkj' | hjk
    · have hpk' := hpk k hk
      have hi : k.val - p < mid.length := by omega
      have hget : mid[k.val - p] = normGate (C.gates.get k) := by
        change (rest.take (j.val - p))[k.val - p] = _
        rw [List.getElem_take]
        exact hrestGet k hpk'
      have hmidSaved := elim_len_lt N a mid start hokMid
        (by omega) ⟨false, hstartFix⟩ ⟨_, hget ▸ List.getElem_mem hi, hkr⟩
      change before.2.length + 1 ≤ pre.length + mid.length at hmidSaved
      omega
    · have hpostSaved := elim_len_lt N a post after hokPost
        (by omega) ⟨false, hafterFix⟩ ⟨_, hpostMem k hjk, hkr⟩
      rw [← hfinal] at hpostSaved
      omega

private def ChainStep (C : Circuit) (n a : ℕ) (j : Fin C.gates.length) : Prop :=
  reads C a j ∧
  (∀ j', reads C a j' → j' = j) ∧
  (C.gates.get j).op = GateOp.or ∧
  (C.gates.get j).inputs.length = 2 ∧
  (∃ w ∈ (C.gates.get j).inputs, w ≠ a ∧ w < n + 1 + j.val)

private theorem ChainStep.read {C n a j} (h : ChainStep C n a j) : reads C a j := h.1

private theorem ChainStep.unique {C n a j} (h : ChainStep C n a j) :
    ∀ j', reads C a j' → j' = j := h.2.1

private theorem ChainStep.op {C n a j} (h : ChainStep C n a j) :
    (C.gates.get j).op = GateOp.or := h.2.2.1

private theorem ChainStep.arity {C n a j} (h : ChainStep C n a j) :
    (C.gates.get j).inputs.length = 2 := h.2.2.2.1

private theorem ChainStep.side {C n a j} (h : ChainStep C n a j) :
    ∃ w ∈ (C.gates.get j).inputs, w ≠ a ∧ w < n + 1 + j.val := h.2.2.2.2

private theorem ChainStep.mem {C : Circuit} {n a : ℕ} {j : Fin C.gates.length}
    (h : ChainStep C n a j) : a ∈ (C.gates.get j).inputs := by
  rcases h.read with ⟨hn, _⟩ | ⟨_, hm⟩
  · rw [h.op] at hn
    cases hn
  · exact hm

private theorem ChainStep.readSide {C : Circuit} {n a w : ℕ}
    {j : Fin C.gates.length} (h : ChainStep C n a j)
    (hm : w ∈ (C.gates.get j).inputs) : reads C w j :=
  Or.inr ⟨by rw [h.op]; simp, hm⟩

private def ChainSegment (C : Circuit) (n a k : ℕ)
    (c : Fin (k + 1) → Fin C.gates.length) : Prop :=
  StrictMono c ∧
  C.output = n + 1 + (c (Fin.last k)).val ∧
  ChainStep C n a (c 0) ∧
  (∀ i : Fin k, ChainStep C n (n + 1 + (c i.castSucc).val) (c i.succ))

private theorem ChainSegment.mono {C n a k c} (h : ChainSegment C n a k c) :
    StrictMono c := h.1

private theorem ChainSegment.output {C n a k c} (h : ChainSegment C n a k c) :
    C.output = n + 1 + (c (Fin.last k)).val := h.2.1

private theorem ChainSegment.first {C n a k c} (h : ChainSegment C n a k c) :
    ChainStep C n a (c 0) := h.2.2.1

private theorem ChainSegment.next {C n a k c} (h : ChainSegment C n a k c) :
    ∀ i : Fin k, ChainStep C n (n + 1 + (c i.castSucc).val) (c i.succ) := h.2.2.2

private theorem buildChainSegment (C : Circuit) (n : ℕ) (P : ℕ → Prop)
    (hvalid : ∀ (a : ℕ) (j : Fin C.gates.length), reads C a j → a < n + 1 + j.val)
    (hnext : ∀ a, P a → a ≠ C.output → ∃ j : Fin C.gates.length,
      reads C a j ∧ (∀ j', reads C a j' → j' = j) ∧
      (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
      (∃ w ∈ (C.gates.get j).inputs, w ≠ a ∧ w < n + 1 + j.val) ∧ P (n + 1 + j.val)) :
    ∀ a, P a → a ≠ C.output →
      ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
        ChainSegment C n a k c ∧ P C.output := by
  have build : ∀ t a : ℕ, t = n + 1 + C.gates.length - a → P a → a ≠ C.output →
      ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
        ChainSegment C n a k c ∧ P C.output := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro a ht ha hne
      obtain ⟨j, hjr, hju, hjo, hjl, hjw, hjp⟩ := hnext a ha hne
      have hstep : ChainStep C n a j := ⟨hjr, hju, hjo, hjl, hjw⟩
      have haj := hvalid a j hjr
      have hjlt := j.isLt
      by_cases hout : n + 1 + j.val = C.output
      · refine ⟨0, fun _ => j, ⟨?_, hout.symm, hstep, fun i => Fin.elim0 i⟩, ?_⟩
        · intro p q hpq
          have hp := p.isLt
          have hq := q.isLt
          exfalso
          change p.val < q.val at hpq
          omega
        · rwa [hout] at hjp
      · have hsmaller : n + 1 + C.gates.length - (n + 1 + j.val) < t := by omega
        obtain ⟨k, d, hd, hp⟩ :=
          ih _ hsmaller (n + 1 + j.val) rfl hjp hout
        let c : Fin (k + 2) → Fin C.gates.length := Fin.cons j d
        refine ⟨k + 1, c, ⟨?_, ?_, ?_, ?_⟩, hp⟩
        · have hjd : j < d 0 := by
            have hh := hvalid (n + 1 + j.val) (d 0) hd.first.read
            change j.val < (d 0).val
            omega
          intro p
          refine Fin.cases ?_ (fun p' => ?_) p
          · intro q
            refine Fin.cases ?_ (fun q' => ?_) q
            · intro h
              exact (lt_irrefl _ h).elim
            · intro _
              simpa only [c, Fin.cons_zero, Fin.cons_succ] using
                hjd.trans_le (hd.mono.monotone (Fin.zero_le q'))
          · intro q
            refine Fin.cases ?_ (fun q' => ?_) q
            · intro h
              change p'.val + 1 < 0 at h
              omega
            · intro h
              have hh : p' < q' := by
                change p'.val + 1 < q'.val + 1 at h
                change p'.val < q'.val
                omega
              simpa only [c, Fin.cons_succ] using hd.mono hh
        · simpa only [show Fin.last (k + 1) = (Fin.last k).succ from rfl,
            c, Fin.cons_succ] using hd.output
        · simpa only [c, Fin.cons_zero] using hstep
        · intro i
          refine Fin.cases ?_ (fun i' => ?_) i
          · change ChainStep C n (n + 1 + (c 0).val) (c (Fin.succ 0))
            simpa only [c, Fin.cons_zero, Fin.cons_succ] using hd.first
          · have he : i'.succ.castSucc = i'.castSucc.succ := Fin.ext rfl
            simpa only [he, c, Fin.cons_succ] using hd.next i'
  intro a ha hne
  exact build _ a rfl ha hne

private theorem chainFrom (C : Circuit) (n : ℕ) (P : ℕ → Prop) (hstart : P n)
    (hvalid : ∀ (a : ℕ) (j : Fin C.gates.length), reads C a j → a < n + 1 + j.val)
    (hterminal : ∀ a, P a → a = C.output → a = n + C.gates.length)
    (hnotStart : C.output ≠ n)
    (hnext : ∀ a, P a → a ≠ C.output → ∃ j : Fin C.gates.length,
      reads C a j ∧ (∀ j', reads C a j' → j' = j) ∧
      (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
      (∃ w ∈ (C.gates.get j).inputs, w ≠ a ∧ w < n + 1 + j.val) ∧ P (n + 1 + j.val)) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = n + 1 + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧
        (C.gates.get (c i)).inputs.length = 2) ∧
      n ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j : Fin C.gates.length, reads C n j → j = c 0) ∧
      (∀ (i : Fin k) (j : Fin C.gates.length),
        reads C (n + 1 + (c i.castSucc).val) j → j = c i.succ) ∧
      (∀ j : Fin C.gates.length,
        Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
          b = n + 1 + j.val ∧ reads C a j) n (n + 1 + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs,
        w ≠ n ∧ w < n + 1 + (c 0).val ∧
        ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
          b = n + 1 + j.val ∧ reads C a j) n w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧
        ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
          b = n + 1 + j.val ∧ reads C a j) n w) := by
  obtain ⟨k, c, hc, hp⟩ := buildChainSegment C n P hvalid hnext n hstart (Ne.symm hnotStart)
  let wire (j : Fin C.gates.length) := n + 1 + j.val
  let edge (a b : ℕ) := ∃ j : Fin C.gates.length, b = wire j ∧ reads C a j
  have hout := hterminal C.output hp rfl
  have heq := hc.output
  have hlast : (c (Fin.last k)).val + 1 = C.gates.length := by omega
  have hwi : Function.Injective wire := by
    intro i j hij
    apply Fin.ext
    dsimp [wire] at hij
    omega
  have successor (i : Fin (k + 1)) (j : Fin C.gates.length)
      (hj : reads C (wire (c i)) j) :
      ∃ q : Fin k, q.castSucc = i ∧ c q.succ = j := by
    by_cases hi : i.val < k
    · let q : Fin k := ⟨i.val, hi⟩
      have hq : q.castSucc = i := Fin.ext rfl
      refine ⟨q, hq, ((hc.next q).unique j ?_).symm⟩
      simpa only [hq, wire] using hj
    · have hir := i.isLt
      have hq : i = Fin.last k := by
        apply Fin.ext
        change i.val = k
        omega
      have hlt := hvalid (wire (c i)) j hj
      rw [hq] at hlt
      have hjlt := j.isLt
      dsimp [wire] at hlt
      omega
  have reached : ∀ i : Fin (k + 1), Relation.TransGen edge n (wire (c i)) := by
    intro i
    refine Fin.induction ?_ (fun q hq => ?_) i
    · exact Relation.TransGen.single ⟨c 0, rfl, hc.first.read⟩
    · exact Relation.TransGen.tail hq ⟨c q.succ, rfl, (hc.next q).read⟩
  have onChain {b : ℕ} (h : Relation.TransGen edge n b) :
      ∃ i : Fin (k + 1), b = wire (c i) := by
    induction h with
    | single he =>
      obtain ⟨j, rfl, hr⟩ := he
      exact ⟨0, congrArg wire (hc.first.unique j hr)⟩
    | tail _ he ih =>
      obtain ⟨j, rfl, hj⟩ := he
      obtain ⟨i, hi⟩ := ih
      rw [hi] at hj
      obtain ⟨q, _, hq⟩ := successor i j hj
      exact ⟨q.succ, congrArg wire hq.symm⟩
  have gateShape (i : Fin (k + 1)) :
      (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2 := by
    refine Fin.cases ?_ (fun q => ?_) i
    · exact ⟨hc.first.op, hc.first.arity⟩
    · exact ⟨(hc.next q).op, (hc.next q).arity⟩
  refine ⟨k, c, hc.mono, hlast, hc.output, gateShape, hc.first.mem,
    fun i => (hc.next i).mem, hc.first.unique, fun i => (hc.next i).unique, ?_, ?_, ?_⟩
  · intro j
    constructor
    · intro h
      obtain ⟨i, he⟩ := onChain h
      exact ⟨i, (hwi he).symm⟩
    · rintro ⟨i, rfl⟩
      exact reached i
  · obtain ⟨w, hm, hn, hl⟩ := hc.first.side
    refine ⟨w, hm, hn, hl, ?_⟩
    intro hw
    obtain ⟨i, rfl⟩ := onChain hw
    obtain ⟨q, _, hq⟩ := successor i (c 0) (hc.first.readSide hm)
    have hh := hc.mono.injective hq
    have hv := congrArg Fin.val hh
    change q.val + 1 = 0 at hv
    omega
  · intro i
    obtain ⟨w, hm, hn, hl⟩ := (hc.next i).side
    have hr := (hc.next i).readSide hm
    refine ⟨w, hm, hn, ?_, hl, ?_⟩
    · intro hw
      rw [hw] at hr
      have hh := hc.mono.injective (hc.first.unique (c i.succ) hr)
      have hv := congrArg Fin.val hh
      change i.val + 1 = 0 at hv
      omega
    · intro hw
      obtain ⟨j, hj⟩ := onChain hw
      rw [hj] at hr
      obtain ⟨q, hq, hsucc⟩ := successor j (c i.succ) hr
      have hh := hc.mono.injective hsucc
      have hqi : q = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hh
        change q.val + 1 = i.val + 1 at hv
        omega
      apply hn
      calc
        w = wire (c j) := hj
        _ = n + 1 + (c i.castSucc).val := by rw [← hq, hqi]
private def prefixW (n : ℕ) (C : Circuit) (p : ℕ) (x : Fin (n + 1) → Bool) : List Bool :=
  wiresFrom ((C.gates.map normGate).take p) (List.ofFn x)

private def forceLast {n : ℕ} (x : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (fun i => x i.castSucc) true

private theorem prefix_length (n : ℕ) (C : Circuit) (p : ℕ) (hp : p ≤ C.gates.length)
    (x : Fin (n + 1) → Bool) : (prefixW n C p x).length = n + 1 + p := by
  simp [prefixW, length_wiresFrom, Nat.min_eq_left hp]

private theorem prefix_cons (n : ℕ) (C : Circuit) (j : Fin C.gates.length)
    (x : Fin (n + 1) → Bool) :
    prefixW n C (j.val + 1) x =
      wiresFrom [normGate (C.gates.get j)] (prefixW n C j.val x) := by
  unfold prefixW
  rw [List.take_succ_eq_append_getElem (by simpa using j.isLt), wiresFrom_append]
  simp

private theorem prefix_segment (n : ℕ) (C : Circuit) (p q : ℕ) (hpq : p ≤ q)
    (x : Fin (n + 1) → Bool) :
    prefixW n C q x =
      wiresFrom (((C.gates.map normGate).drop p).take (q - p)) (prefixW n C p x) := by
  unfold prefixW
  conv_lhs => rw [show q = p + (q - p) by omega]
  rw [List.take_add, wiresFrom_append]

private theorem prefix_suffix (n : ℕ) (C : Circuit) (p : ℕ) (x : Fin (n + 1) → Bool) :
    (wiresFrom ((C.gates.map normGate).drop p) (prefixW n C p x)).getD C.output false
      = circuitFun (n + 1) C x := by
  unfold prefixW
  rw [← wiresFrom_append, List.take_append_drop, wiresFrom_norm]
  rfl

private theorem read_in_suffix (C : Circuit) (p : ℕ) (g : Gate)
    (hg : g ∈ (C.gates.map normGate).drop p) :
    ∃ j : Fin C.gates.length, p ≤ j.val ∧ g = normGate (C.gates.get j) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hg
  have hij : p + i < C.gates.length := by
    simp [List.length_drop] at hi
    omega
  refine ⟨⟨p + i, hij⟩, by simp, ?_⟩
  simpa using he.symm

private theorem read_in_segment (C : Circuit) (p d : ℕ) (g : Gate)
    (hg : g ∈ ((C.gates.map normGate).drop p).take d) :
    ∃ j : Fin C.gates.length, p ≤ j.val ∧ j.val < p + d ∧ g = normGate (C.gates.get j) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hg
  have hil : i < min d (C.gates.length - p) := by simpa using hi
  have hil' := Nat.lt_min.mp hil
  have hij : p + i < C.gates.length := by omega
  refine ⟨⟨p + i, hij⟩, by simp, by simpa using hil'.1, ?_⟩
  simpa using he.symm

private theorem prefix_zero_off (n : ℕ) (C : Circuit) (x : Fin (n + 1) → Bool)
    (i : ℕ) (hi : i ≠ n) :
    (prefixW n C 0 x).getD i false = (prefixW n C 0 (forceLast x)).getD i false := by
  change (List.ofFn x).getD i false = (List.ofFn (forceLast x)).getD i false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hib : i < n + 1
  · have hin : i < n := by omega
    have he : (⟨i, hib⟩ : Fin (n + 1)) = (⟨i, hin⟩ : Fin n).castSucc := rfl
    simp [List.getElem?_ofFn, hib, he, forceLast]
  · simp [List.getElem?_ofFn, hib]

private theorem getD_set_same {α : Type} (xs : List α) (i : ℕ) (v d : α)
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]

private theorem getD_set_other {α : Type} (xs : List α) (i j : ℕ) (v d : α)
    (h : i ≠ j) : (xs.set i v).getD j d = xs.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

private def active (n : ℕ) (C : Circuit) (a : ℕ) : Prop :=
  n ≤ a ∧ a ≤ n + C.gates.length ∧ ∃ S : Set ℕ,
    C.output ∉ S ∧
    (∀ g ∈ (C.gates.map normGate).drop (a - n), ∀ u ∈ g.inputs, u ∉ S) ∧
    (∀ x, (prefixW n C (a - n) (forceLast x)).getD a false = true) ∧
    ∀ x i, i ∉ S → i ≠ a →
      (prefixW n C (a - n) x).getD i false =
        (prefixW n C (a - n) (forceLast x)).getD i false

private theorem active_input (n : ℕ) (C : Circuit) : active n C n := by
  refine ⟨le_rfl, by omega, ∅, by simp, by simp, ?_, ?_⟩
  · intro x
    change (List.ofFn (forceLast x)).getD n false = true
    rw [ofFn_snoc]
    exact getD_snoc_len _ _ _ _ (by simp)
  · intro x i _ hi
    simpa using prefix_zero_off n C x i hi

private theorem active_cut_true (n : ℕ) (C : Circuit) (a : ℕ)
    (ha : active n C a)
    (hF : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C (forceLast x) = true) :
    ∀ x, cutVal n C a true x = true := by
  obtain ⟨han, hal, S, hSout, hSread, haw, hag⟩ := ha
  intro x
  let p := a - n
  let u := prefixW n C p x
  let v := prefixW n C p (forceLast x)
  have hp : p ≤ C.gates.length := by dsimp [p]; omega
  have hlu : u.length = n + 1 + p := prefix_length n C p hp x
  have hlv : v.length = n + 1 + p := prefix_length n C p hp _
  have haz : a < u.length := by dsimp [p] at hlu; omega
  have heq : ∀ i, i ∉ S → (u.set a true).getD i false = v.getD i false := by
    intro i hi
    by_cases h : i = a
    · subst i
      rw [getD_set_same _ _ _ _ haz]
      exact (haw x).symm
    · rw [getD_set_other _ _ _ _ _ h.symm]
      exact hag x i hi h
  have he := wires_agree ((C.gates.map normGate).drop p) (fun i => i ∈ S)
    (u.set a true) v (by simpa using hlu.trans hlv.symm) heq hSread C.output hSout
  change (wiresFrom ((C.gates.map normGate).drop p) (u.set a true)).getD C.output false = true
  rw [he]
  exact (prefix_suffix n C p (forceLast x)).trans (hF x)

private theorem active_advance (n : ℕ) (C : Circuit) (a : ℕ) (j : Fin C.gates.length)
    (ha : active n C a) (haj : a < n + 1 + j.val)
    (hun : ∀ k, reads C a k → k = j)
    (hop : (C.gates.get j).op = GateOp.or) (hmem : a ∈ (C.gates.get j).inputs)
    (hout : a ≠ C.output) : active n C (n + 1 + j.val) := by
  obtain ⟨han, hal, S, hSout, hSread, haw, hag⟩ := ha
  let p := a - n
  let b := n + 1 + j.val
  have hpj : p ≤ j.val := by dsimp [p]; omega
  have hb : b - n = j.val + 1 := by dsimp [b]; omega
  have hagmid (x : Fin (n + 1) → Bool) (i : ℕ) (hi : i ∉ insert a S) :
      (prefixW n C j.val x).getD i false =
        (prefixW n C j.val (forceLast x)).getD i false := by
    rw [prefix_segment n C p j.val hpj, prefix_segment n C p j.val hpj]
    apply wires_agree _ (fun i => i ∈ insert a S)
    · rw [prefix_length n C p (le_trans hpj j.isLt.le),
          prefix_length n C p (le_trans hpj j.isLt.le)]
    · intro w hw
      exact hag x w (fun h => hw (Set.mem_insert_of_mem _ h))
        (fun h => hw (Set.mem_insert_iff.mpr (Or.inl h)))
    · intro g hg w hw
      obtain ⟨k, hpk, hkj, rfl⟩ := read_in_segment C p (j.val - p) g hg
      have hg' : normGate (C.gates.get k) ∈ (C.gates.map normGate).drop p :=
        List.mem_of_mem_take hg
      intro hbad
      rcases Set.mem_insert_iff.mp hbad with he | hs
      · subst w
        have e := hun k ((reads_norm_iff C a k).2 hw)
        subst k
        omega
      · exact hSread _ hg' _ hw hs
    · exact hi
  refine ⟨by dsimp [b]; omega, by dsimp [b]; omega, insert a S, ?_, ?_, ?_, ?_⟩
  · intro ho
    rcases Set.mem_insert_iff.mp ho with e | he
    · exact hout e.symm
    · exact hSout he
  · rw [hb]
    intro g hg w hw hbad
    obtain ⟨k, hk, rfl⟩ := read_in_suffix C (j.val + 1) g hg
    rcases Set.mem_insert_iff.mp hbad with he | hs
    · subst w
      have e := hun k ((reads_norm_iff C a k).2 hw)
      subst k
      omega
    · have hdrop : (C.gates.map normGate).drop (j.val + 1) =
          ((C.gates.map normGate).drop p).drop (j.val + 1 - p) := by
        rw [List.drop_drop, show p + (j.val + 1 - p) = j.val + 1 by omega]
      rw [hdrop] at hg
      exact hSread _ (List.mem_of_mem_drop hg) _ hw hs
  · rw [hb]
    intro x
    rw [prefix_cons]
    have hn : normGate (C.gates.get j) = C.gates.get j :=
      normGate_of_ne_not _ (by simp [hop])
    rw [hn]
    let v := prefixW n C j.val (forceLast x)
    have hv : v.length = b := prefix_length n C _ j.isLt.le _
    have hpre := prefix_segment n C p j.val hpj (forceLast x)
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix (((C.gates.map normGate).drop p).take (j.val - p))
      (prefixW n C p (forceLast x))
    have hpa : a < (prefixW n C p (forceLast x)).length := by
      rw [prefix_length n C p (le_trans hpj j.isLt.le)]
      dsimp [p]
      omega
    have hvtrue : v.getD a false = true := by
      change (prefixW n C j.val (forceLast x)).getD a false = true
      rw [hpre, ht, List.getD_append _ _ _ _ hpa]
      exact haw x
    change (v ++ [(C.gates.get j).op.eval
      ((C.gates.get j).inputs.map fun i => v.getD i false)]).getD b false = true
    rw [getD_snoc_len _ _ _ _ hv, hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨true, ⟨a, hmem, hvtrue⟩, rfl⟩
  · rw [hb]
    intro x i hi hib
    rw [prefix_cons, prefix_cons]
    have hlen (z : Fin (n + 1) → Bool) : (prefixW n C j.val z).length = b :=
      prefix_length n C _ j.isLt.le _
    change (_ ++ [_]).getD i false = (_ ++ [_]).getD i false
    rw [getD_snoc_ne _ _ _ _ (by simpa [hlen x] using hib),
        getD_snoc_ne _ _ _ _ (by simpa [hlen (forceLast x)] using hib)]
    exact hagmid x i hi

private theorem output_dep (n : ℕ) (C : Circuit)
    (hd : ∃ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C (forceLast x)) :
    n ≤ C.output ∧ (C.output = n ∨ ∃ j : Fin C.gates.length, reads C n j) := by
  obtain ⟨x, hx⟩ := hd
  have hv := prefix_zero_off n C x
  constructor
  · by_contra h
    have he : C.output < n := by omega
    have hpre (z : Fin (n + 1) → Bool) :
        circuitFun (n + 1) C z = (prefixW n C 0 z).getD C.output false := by
      rw [← prefix_suffix n C 0 z]
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix ((C.gates.map normGate).drop 0) (prefixW n C 0 z)
      rw [ht, List.getD_append _ _ _ _ (by
        rw [prefix_length _ _ _ (Nat.zero_le _)]; omega)]
    apply hx
    rw [hpre, hpre, hv C.output (by omega)]
  · by_cases he : C.output = n
    · exact Or.inl he
    · right
      by_contra hn
      have hgs : ∀ g ∈ (C.gates.map normGate).drop 0, ∀ i ∈ g.inputs, i ≠ n := by
        intro g hg i hi h
        subst i
        obtain ⟨j, _, rfl⟩ := read_in_suffix C 0 g hg
        exact hn ⟨j, (reads_norm_iff C n j).2 hi⟩
      have heq := wires_agree ((C.gates.map normGate).drop 0) (fun i => i = n)
        (prefixW n C 0 x) (prefixW n C 0 (forceLast x))
        (by rw [prefix_length _ _ _ (Nat.zero_le _), prefix_length _ _ _ (Nat.zero_le _)])
        hv hgs C.output he
      rw [prefix_suffix, prefix_suffix] at heq
      exact hx heq
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  classical
  intro n C H hmin hH hshape
  have hslice (y : Fin n → Bool) (b : Bool) :
      circuitFun (n + 1) C (Fin.snoc y b) = (b || H y) := by
    rw [hshape]
    simp
  obtain ⟨y, z, hyz⟩ := hH
  have hnc : ∃ x x' : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
    refine ⟨Fin.snoc y false, Fin.snoc z false, ?_⟩
    simpa [hslice] using hyz
  have hF (x : Fin (n + 1) → Bool) : circuitFun (n + 1) C (forceLast x) = true := by
    simp [forceLast, hslice]
  have hzero : ∃ l, H l = false := by
    cases he : H y with
    | false => exact ⟨y, he⟩
    | true =>
      refine ⟨z, ?_⟩
      cases hf : H z <;> simp_all
  obtain ⟨l, hl⟩ := hzero
  have hdep : ∃ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x ≠ circuitFun (n + 1) C (forceLast x) := by
    exact ⟨Fin.snoc l false, by simp [hF, hslice, hl]⟩
  have houtn : C.output ≠ n := by
    intro he
    have hc (x : Fin (n + 1) → Bool) : circuitFun (n + 1) C x = x (Fin.last n) := by
      rw [← prefix_suffix n C 0, he]
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix ((C.gates.map normGate).drop 0) (prefixW n C 0 x)
      rw [ht, List.getD_append _ _ _ _ (by rw [prefix_length _ _ _ (Nat.zero_le _)]; omega)]
      change (List.ofFn x).getD n false = x (Fin.last n)
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    apply hyz
    simpa [hslice] using (hc (Fin.snoc y false)).trans (hc (Fin.snoc z false)).symm
  have hinit := output_dep n C hdep
  have hout := outputLast n C hmin hnc (by omega)
  have hvalid := cleanReads n C hmin hnc
  have hlive (j : Fin C.gates.length) (hne : n + 1 + j.val ≠ C.output) :
      ∃ k : Fin C.gates.length, reads C (n + 1 + j.val) k := by
    obtain ⟨k, _, hk⟩ := liveGate n C hmin hnc j hne
    exact ⟨k, hk⟩
  refine chainFrom C n (active n C) (active_input n C) hvalid
    (fun a _ ha => ha.trans hout) houtn ?_
  intro a ha hne
  have hreader : ∃ j : Fin C.gates.length, reads C a j := by
    by_cases he : a = n
    · subst a
      exact hinit.2.resolve_left houtn
    · have hlow := ha.1
      have hhigh := ha.2.1
      let j : Fin C.gates.length := ⟨a - (n + 1), by omega⟩
      have hj : n + 1 + j.val = a := by dsimp [j]; omega
      rw [← hj]
      exact hlive j (by rwa [hj])
  obtain ⟨j, hj⟩ := hreader
  have hcut := cutStep n C hmin
    (fun j a ha => hvalid a j ((reads_norm_iff C a j).2 ha)) hlive hnc
    a ha.1 ha.2.1 hne (active_cut_true n C a ha hF) j hj
  obtain ⟨⟨hop, hlen, hmem, hside⟩, hun⟩ := hcut
  exact ⟨j, hj, hun, hop, hlen, hside, active_advance n C a j ha (hvalid a j hj) hun hop hmem hne⟩

end PEqualNP.Outside.Meta568
