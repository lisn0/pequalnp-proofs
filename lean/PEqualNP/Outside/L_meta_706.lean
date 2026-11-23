import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_706

open PEqualNP.AndCount

-- Fuel stabilization follows the argument in L-meta-564.
private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private def signal {n k : ℕ} (U A : Finset (Fin n)) (P : Finset (Fin k))
    (val : Fin k → Bool) : Prop :=
  (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true

private theorem gate_spec {n : ℕ} (C : AndCountCircuit n) (hw : C.WellFormed)
    (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔ signal U (C.leftVars i) (C.leftGates i) (C.gateVal U) ∧
      signal U (C.rightVars i) (C.rightGates i) (C.gateVal U) := by
  rw [gateVal_eq, Bool.and_eq_true]
  simp only [signal, AndCountCircuit.sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases hr with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
    · rcases hr with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩

private def expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) : Finset (Fin n) :=
  A ∪ if i ∈ P then B else ∅

private def expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) :
    Finset (Fin m) :=
  Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)

private theorem mem_expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) (v : Fin n) :
    v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
  by_cases h : i ∈ P <;> simp [expandVars, h]

private theorem mem_expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1)))
    (k : Fin m) :
    k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
  simp [expandRefs]

private theorem signal_expand {n m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin n))
    (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool)
    (before : ∀ j ∈ F, j < i) (expand : val i = true ↔ signal U B F val)
    (agree : ∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) :
    signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨k, hk, ht⟩)
    · rcases (mem_expandVars i B A P v).mp hv with hvA | ⟨hi, hvB⟩
      · exact Or.inl ⟨v, hvA, hu⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inl ⟨v, hvB, hu⟩)⟩
    · rw [agree k hk] at ht
      rcases (mem_expandRefs i F P k).mp hk with hP | ⟨hi, hF⟩
      · exact Or.inr ⟨_, hP, ht⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inr ⟨_, hF, ht⟩)⟩
  · rintro (⟨v, hv, hu⟩ | ⟨j, hj, ht⟩)
    · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inl hv), hu⟩
    · by_cases hji : j = i
      · subst j
        rcases expand.mp ht with ⟨v, hv, hu⟩ | ⟨l, hl, ht'⟩
        · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
          have hk := (mem_expandRefs i F P k).mpr (Or.inr ⟨hj, hl⟩)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hk := (mem_expandRefs i F P k).mpr (Or.inl hj)
        exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩

private theorem eliminate {n m : ℕ}
    (lv rv : Fin (m + 1) → Finset (Fin n)) (lg rg : Fin (m + 1) → Finset (Fin (m + 1)))
    (ov : Finset (Fin n)) (og : Finset (Fin (m + 1))) (i : Fin (m + 1))
    (D : Set (Finset (Fin n))) (B : Finset (Fin n)) (F : Finset (Fin (m + 1)))
    (hw : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) (before : ∀ j ∈ F, j < i)
    (same : ∀ U ∈ D, (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U i = true ↔
      signal U B F ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U)) :
    ∃ C' : AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ m + 1 ∧
      ∀ U ∈ D, C'.eval U = (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).eval U := by
  let C : AndCountCircuit n := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
  let C' : AndCountCircuit n :=
    ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
      fun j => expandRefs i F (lg (i.succAbove j)),
      fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
      fun j => expandRefs i F (rg (i.succAbove j)),
      expandVars i B ov og, expandRefs i F og⟩
  have lt_ref (j k : Fin m) (P : Finset (Fin (m + 1)))
      (old : ∀ l ∈ P, l < i.succAbove j) (hk : k ∈ expandRefs i F P) : k < j := by
    apply Fin.succAbove_lt_succAbove_iff.mp
    rcases (mem_expandRefs i F P k).mp hk with hp | ⟨hi, hf⟩
    · exact old _ hp
    · exact (before _ hf).trans (old i hi)
  have hw' : C'.WellFormed := by
    intro j
    exact ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
      fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
  refine ⟨C', hw', le_rfl, ?_⟩
  intro U hU
  have values (j : Fin m) : C'.gateVal U j = C.gateVal U (i.succAbove j) := by
    induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
    | h j ih =>
      rw [Bool.eq_iff_iff, gate_spec C' hw', gate_spec C hw]
      exact and_congr
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)

end PEqualNP.Outside.L_meta_706

theorem PEqualNP.Outside.L_meta_706 :
    ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  rintro n ⟨s, lv, lg, rv, rg, ov, og⟩
  cases s with
  | zero =>
    intro _ _ i
    exact Fin.elim0 i
  | succ m =>
    intro hw D i B F before same
    exact PEqualNP.Outside.L_meta_706.eliminate lv rv lg rg ov og i D B F hw before same
