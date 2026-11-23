import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_635

open PEqualNP.AndCount

private def adjacent (a b : Fin 10) : Prop :=
  (a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) ∨
  (a = 2 ∧ b = 3 ∨ a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 4 ∨ a = 4 ∧ b = 3) ∨
  (a = 4 ∧ b = 0 ∨ a = 0 ∧ b = 4) ∨ (a = 0 ∧ b = 5 ∨ a = 5 ∧ b = 0) ∨
  (a = 1 ∧ b = 6 ∨ a = 6 ∧ b = 1) ∨ (a = 2 ∧ b = 7 ∨ a = 7 ∧ b = 2) ∨
  (a = 3 ∧ b = 8 ∨ a = 8 ∧ b = 3) ∨ (a = 4 ∧ b = 9 ∨ a = 9 ∧ b = 4) ∨
  (a = 5 ∧ b = 7 ∨ a = 7 ∧ b = 5) ∨ (a = 6 ∧ b = 8 ∨ a = 8 ∧ b = 6) ∨
  (a = 7 ∧ b = 9 ∨ a = 9 ∧ b = 7) ∨ (a = 8 ∧ b = 5 ∨ a = 5 ∧ b = 8) ∨
  (a = 9 ∧ b = 6 ∨ a = 6 ∧ b = 9)

private def witness : AndCountCircuit 10 where
  size := 6
  leftVars i := {(![1, 3, 4, 5, 6, 7] : Fin 6 → Fin 10) i}
  rightVars := ![{0, 2, 6}, {2, 4, 8}, {3, 0, 9}, {0, 7, 8}, {1, 8, 9}, {2, 5, 9}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private theorem witness_wellFormed : witness.WellFormed := by
  intro i
  simp [witness]

private theorem witness_gate (I : Finset (Fin 10)) (i : Fin witness.size) :
    witness.gateVal I i = true ↔
      (∃ a ∈ witness.leftVars i, a ∈ I) ∧ (∃ b ∈ witness.rightVars i, b ∈ I) := by
  change (_ && _) = true ↔ _
  simp only [Bool.and_eq_true, AndCountCircuit.sideTrue, decide_eq_true_eq]
  have hl : witness.leftGates i = ∅ := rfl
  have hr : witness.rightGates i = ∅ := rfl
  simp [hl, hr]

private theorem witness_eval (I : Finset (Fin 10)) :
    witness.eval I = true ↔ ∃ i : Fin witness.size, witness.gateVal I i = true := by
  unfold AndCountCircuit.eval
  have hv : witness.outVars = ∅ := rfl
  have hg : witness.outGates = Finset.univ := rfl
  simp [hv, hg]

private theorem covered (a b : Fin 10) : adjacent a b ↔
    ∃ i : Fin witness.size,
      (a ∈ witness.leftVars i ∧ b ∈ witness.rightVars i) ∨
      (b ∈ witness.leftVars i ∧ a ∈ witness.rightVars i) := by
  fin_cases a <;> fin_cases b <;> unfold adjacent <;> decide

private theorem witness_computes (G : SimpleGraph (Fin 10))
    (adj : ∀ a b, G.Adj a b ↔ adjacent a b) : witness.Computes G := by
  intro I
  rw [witness_eval]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨⟨a, ha, haI⟩, ⟨b, hb, hbI⟩⟩ := (witness_gate I i).mp hi
    exact ⟨a, haI, b, hbI, (adj a b).mpr ((covered a b).mpr ⟨i, Or.inl ⟨ha, hb⟩⟩)⟩
  · rintro ⟨a, haI, b, hbI, hab⟩
    obtain ⟨i, h | h⟩ := (covered a b).mp ((adj a b).mp hab)
    · exact ⟨i, (witness_gate I i).mpr ⟨⟨a, h.1, haI⟩, ⟨b, h.2, hbI⟩⟩⟩
    · exact ⟨i, (witness_gate I i).mpr ⟨⟨b, h.1, hbI⟩, ⟨a, h.2, haI⟩⟩⟩

private theorem upper (G : SimpleGraph (Fin 10))
    (h : G.edgeSet = {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}) :
    ∃ C : AndCountCircuit 10, C.WellFormed ∧
      (∀ I : Finset (Fin 10), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ C.size = 6 := by
  have adj (a b : Fin 10) : G.Adj a b ↔ adjacent a b := by
    rw [← SimpleGraph.mem_edgeSet, h]
    simp only [adjacent, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
  have computes := witness_computes G adj
  refine ⟨witness, witness_wellFormed, ?_, rfl⟩
  intro I independent dominates
  constructor
  · rw [← Bool.not_eq_true]
    intro hI
    obtain ⟨a, haI, b, hbI, hab⟩ := (computes I).mp hI
    exact independent a haI b hbI hab
  · intro u hu
    obtain ⟨v, hvI, huv⟩ := dominates u hu
    exact (computes (insert u I)).mpr ⟨u, by simp, v, by simp [hvI], huv⟩

end PEqualNP.Outside.L_meta_635
