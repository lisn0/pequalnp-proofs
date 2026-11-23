import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763

open PEqualNP.MetaComplexity

private abbrev graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ ([(0, 1), (0, 2), (1, 3), (4, 5)] : List (Fin 6 × Fin 6))

private def cover : Finset (Fin 6) := {0, 1, 4}

private abbrev treeGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈
    ([(0, 1), (0, 2), (1, 3), (4, 5), (2, 4)] : List (Fin 6 × Fin 6))

private theorem edges : graph.edgeFinset.card = 4 := by
  decide +kernel

private theorem reachableCenter (v : Fin 6) : treeGraph.Reachable 0 v := by
  have r01 := (show treeGraph.Adj 0 1 by decide).reachable
  have r02 := (show treeGraph.Adj 0 2 by decide).reachable
  have r04 := r02.trans (show treeGraph.Adj 2 4 by decide).reachable
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact r01
  · exact r02
  · exact r01.trans (show treeGraph.Adj 1 3 by decide).reachable
  · exact r04
  · exact r04.trans (show treeGraph.Adj 4 5 by decide).reachable

private theorem acyclic : graph.IsAcyclic := by
  have conn : treeGraph.Connected :=
    SimpleGraph.connected_iff_exists_forall_reachable.mpr ⟨0, reachableCenter⟩
  have htreeEdges : treeGraph.edgeFinset.card = 5 := by decide +kernel
  have hcard : Nat.card treeGraph.edgeSet + 1 = Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, htreeEdges]
    simp
  have tree := SimpleGraph.isTree_iff_connected_and_card.mpr ⟨conn, hcard⟩
  apply tree.isAcyclic.anti
  change ∀ a b : Fin 6, graph.Adj a b → treeGraph.Adj a b
  decide +kernel

private theorem hasEdge : ∃ i j : Fin 6, graph.Adj i j := by
  decide +kernel

private theorem coverMin : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

private theorem covers : ∀ i j : Fin 6, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by
  decide +kernel

private theorem functionEq : ∀ x : Fin 6 → Bool,
    decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) := by
  decide +kernel

theorem exactSize (s : ℕ) :
    HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  rw [← funext functionEq]
  constructor
  · intro h
    have bound := L104 6 3 s graph acyclic hasEdge coverMin h
    rw [edges] at bound
    omega
  · intro hs
    have upper := L105 6 graph cover hasEdge covers
    have h3 : graph.edgeFinset.card + cover.card - 1 = 6 := by decide +kernel
    rw [h3] at upper
    obtain ⟨C, hfan, hsize, heval⟩ := upper
    exact ⟨C, hfan, hsize.trans hs, heval⟩

end PEqualNP.Outside.L_meta_763

theorem PEqualNP.Outside.L_meta_763 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_763.exactSize
