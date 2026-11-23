import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_754

open PEqualNP.MetaComplexity

private abbrev graph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ ([(0, 1), (0, 2), (0, 3), (1, 4)] : List (Fin 5 × Fin 5))

private def cover : Finset (Fin 5) := {0, 1}

private theorem edges : graph.edgeFinset.card = 4 := by
  decide +kernel

private theorem reachableCenter (v : Fin 5) : graph.Reachable 0 v := by
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (show graph.Adj 0 1 by decide).reachable
  · exact (show graph.Adj 0 2 by decide).reachable
  · exact (show graph.Adj 0 3 by decide).reachable
  · exact (show graph.Adj 0 1 by decide).reachable.trans (show graph.Adj 1 4 by decide).reachable

private theorem acyclic : graph.IsAcyclic := by
  have conn : graph.Connected :=
    ⟨fun a b => (reachableCenter a).symm.trans (reachableCenter b), inferInstance⟩
  have hcard : Nat.card graph.edgeSet + 1 = Nat.card (Fin 5) := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, edges]
    simp
  exact (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨conn, hcard⟩).2

private theorem hasEdge : ∃ i j : Fin 5, graph.Adj i j := by
  decide +kernel

private theorem coverMin : ∀ T : Finset (Fin 5),
    (∀ i j : Fin 5, graph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

private theorem covers : ∀ i j : Fin 5, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by
  decide +kernel

private theorem functionEq : ∀ x : Fin 5 → Bool,
    decide (∃ i j : Fin 5, graph.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) := by
  decide +kernel

theorem exactSize (s : ℕ) :
    HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  rw [← funext functionEq]
  constructor
  · intro h
    have bound := L104 5 2 s graph acyclic hasEdge coverMin h
    rw [edges] at bound
    omega
  · intro hs
    have upper := L105 5 graph cover hasEdge covers
    have h3 : graph.edgeFinset.card + cover.card - 1 = 5 := by decide +kernel
    rw [h3] at upper
    obtain ⟨C, hfan, hsize, heval⟩ := upper
    exact ⟨C, hfan, hsize.trans hs, heval⟩

end PEqualNP.Outside.L_meta_754

theorem PEqualNP.Outside.L_meta_754 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_754.exactSize
