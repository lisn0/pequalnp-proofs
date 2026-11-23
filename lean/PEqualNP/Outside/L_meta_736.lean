import Mathlib
import PEqualNP.Defs

-- The wire relabelling argument is adapted from L-meta-571.

namespace PEqualNP.Outside.L_meta_736

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

private lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

private lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

private lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (run gs W) (run (gs.map (relGate n m π)) W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)


private theorem substitute_true (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (cover : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) (gates : List Gate) :
    ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
      (∀ k ∈ O, x.getD (k : ℕ) false = true) →
      (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
      (∀ i : ℕ, (Circuit.wires
          { gates := { op := GateOp.and, inputs := [] } ::
              gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
        = (Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
      (∀ o : ℕ, Circuit.eval
          { gates := { op := GateOp.and, inputs := [] } ::
              gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
        = Circuit.eval { gates := gates, output := o } x) := by
  classical
  let π : Fin n → Fin (n' + 1) := fun k =>
    if h : k ∈ O then Fin.last n' else (Classical.choose ((cover k).mp h)).castSucc
  refine ⟨wmap n (n' + 1) π, ?_⟩
  intro x x' hx hx' ones kept
  have start : Rel n (n' + 1) π x (x' ++ [true]) := by
    refine ⟨by omega, by simp [hx, hx']; omega, ?_⟩
    intro w
    by_cases hw : w < n
    · let k : Fin n := ⟨w, hw⟩
      change (x' ++ [true]).getD (wmap n (n' + 1) π w) false = x.getD (k : ℕ) false
      rw [show wmap n (n' + 1) π w = (π k : ℕ) by simp [wmap, hw, k]]
      by_cases hk : k ∈ O
      · have he : (π k : ℕ) = n' := by simp [π, hk]
        rw [he, ← hx', getD_snoc_eq]
        exact (ones k hk).symm
      · let j := Classical.choose ((cover k).mp hk)
        have ej : e j = k := Classical.choose_spec ((cover k).mp hk)
        have he : (π k : ℕ) = (j : ℕ) := by simp [π, hk, j]
        rw [he, getD_snoc_lt _ _ _ (by simpa [hx'] using j.isLt), ← kept j, ej]
    · rw [show wmap n (n' + 1) π w = w - n + (n' + 1) by simp [wmap, hw]]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have all := (rel_fold n (n' + 1) π gates x (x' ++ [true]) start).2.2
  constructor
  · intro i
    exact all i
  · intro o
    exact all o

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 :
    ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
      (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
      ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
      ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
        (∀ k ∈ O, x.getD (k : ℕ) false = true) →
        (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
        (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
            { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
                gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
          = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
        (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
            { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
                gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
          = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' O e _ cover _ gates
  exact PEqualNP.Outside.L_meta_736.substitute_true n n' O e cover gates
