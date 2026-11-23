import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_752

open PEqualNP.MetaComplexity

private abbrev graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ ([(0, 1), (2, 3)] : List (Fin 4 × Fin 4))

private def cover : Finset (Fin 4) := {0, 2}

private theorem uniqueNeighbor :
    ∀ v a b : Fin 4, graph.Adj v a → graph.Adj v b → a = b := by
  decide +kernel

private theorem acyclic : graph.IsAcyclic := by
  intro v p hp
  exact hp.snd_ne_penultimate
    (uniqueNeighbor v _ _ (p.adj_snd hp.not_nil) (p.adj_penultimate hp.not_nil).symm)

private theorem edges : graph.edgeFinset.card = 2 := by
  decide +kernel

private theorem hasEdge : ∃ i j : Fin 4, graph.Adj i j := by
  decide +kernel

private theorem coverMin : ∀ T : Finset (Fin 4),
    (∀ i j : Fin 4, graph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

private theorem covers : ∀ i j : Fin 4, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by
  decide +kernel

private theorem functionEq : ∀ x : Fin 4 → Bool,
    decide (∃ i j : Fin 4, graph.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 2 && x 3)) := by
  decide +kernel

theorem exactSize (s : ℕ) :
    HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  rw [← funext functionEq]
  constructor
  · intro h
    have bound := L104 4 2 s graph acyclic hasEdge coverMin h
    rw [edges] at bound
    omega
  · intro hs
    have upper := L105 4 graph cover hasEdge covers
    have h3 : graph.edgeFinset.card + cover.card - 1 = 3 := by decide +kernel
    rw [h3] at upper
    obtain ⟨C, hfan, hsize, heval⟩ := upper
    exact ⟨C, hfan, hsize.trans hs, heval⟩

end PEqualNP.Outside.L_meta_752

theorem PEqualNP.Outside.L_meta_752 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s :=
  PEqualNP.Outside.L_meta_752.exactSize
