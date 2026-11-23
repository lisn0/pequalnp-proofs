import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_652_upper

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩,
    ⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 14]⟩,
    ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem computes : ∀ x : Fin 6 → Bool,
    (witness.wires (List.ofFn x)).getD 10 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
    (witness.wires (List.ofFn x)).getD 15 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
    (witness.wires (List.ofFn x)).getD 20 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  decide +kernel

theorem upper : ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧
    ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool,
      (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
      (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
      (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  exact ⟨witness, by simp [PEqualNP.MetaComplexity.FanInTwo, witness], by decide,
    10, 15, 20, computes⟩

end PEqualNP.Outside.L_meta_652_upper
