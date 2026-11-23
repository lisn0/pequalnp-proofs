import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_586_upper

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [3, 13]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [6, 15]⟩,
    ⟨.or, [8, 10]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [19, 16]⟩], 20⟩

private def orGates : Finset ℕ := {1, 3, 5, 7, 9, 10, 11, 12}

private theorem orGateCoverage (j : ℕ) (g : Gate) (hj : witness.gates[j]? = some g)
    (hop : g.op = GateOp.or) : j ∈ orGates := by
  have hjlt : j < 13 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [witness] using this
  interval_cases j <;> simp [witness] at hj <;> subst g <;> simp_all [orGates]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem computes : ∀ x : Fin 8 → Bool,
    (witness.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8,
      (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 5),
        (5, 6), (6, 7), (7, 0)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  decide +kernel

theorem upper : ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    (∃ A : Finset ℕ, A.card ≤ 8 ∧ ∀ (j : ℕ) (g : Gate),
      C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) ∧
    (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8,
      (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 5),
        (5, 6), (6, 7), (7, 0)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  exact ⟨witness, by simp [PEqualNP.MetaComplexity.Monotone2, witness],
    ⟨orGates, by decide, orGateCoverage⟩, computes⟩

end PEqualNP.Outside.L_meta_586_upper
