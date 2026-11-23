import Mathlib

namespace PEqualNP.Outside.L_meta_732

private def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
    (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

private def arcs : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
    (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

private def adj (u v : Fin 8) : Prop :=
  (u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges

private def arc (u v : Fin 8) : Prop := (u.val, v.val) ∈ arcs

private theorem orientation : ∀ u v, adj u v ↔ (arc u v ∨ arc v u) := by
  unfold adj arc
  decide +kernel

private theorem asymmetric : ∀ u v, arc u v → ¬ arc v u := by
  unfold arc
  decide +kernel

private def independentSets : List (Finset (Fin 8)) :=
  [∅, {0}, {1}, {2}, {0, 2}, {1, 2}, {3}, {2, 3}, {4}, {5}, {1, 5}, {2, 5}, {1, 2, 5}, {6}, {3, 6}, {5, 6}, {7}, {0, 7}, {1, 7}, {6, 7}]

private def independent (W : Finset (Fin 8)) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, ¬ adj u v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem listed : ∀ W : Finset (Fin 8), independent W → W ∈ independentSets := by
  unfold independent adj
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem extension :
    ∀ W ∈ independentSets, ∀ K ∈ independentSets, (∀ k ∈ K, k ∉ W) →
      ∃ v : Fin 8, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ arc v k := by
  unfold arc
  decide +kernel

private theorem transfer (E D : Fin 8 → Fin 8 → Prop)
    (he : ∀ u v, E u v ↔ adj u v) (hd : ∀ u v, D u v ↔ arc u v) :
    (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
    ∀ W K : Set (Fin 8),
      (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
      ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [he u v, hd u v, hd v u]
    exact orientation u v
  · intro u v
    rw [hd u v, hd v u]
    exact asymmetric u v
  · intro W K hW disj hK
    let W' : Finset (Fin 8) := Finset.univ.filter (fun v => v ∈ W)
    let K' : Finset (Fin 8) := Finset.univ.filter (fun v => v ∈ K)
    have wmem (v : Fin 8) : v ∈ W' ↔ v ∈ W := by simp [W']
    have kmem (v : Fin 8) : v ∈ K' ↔ v ∈ K := by simp [K']
    have hw' : independent W' := by
      intro u hu v hv h
      exact hW u ((wmem u).mp hu) v ((wmem v).mp hv) ((he u v).mpr h)
    have hk' : independent K' := by
      intro u hu v hv h
      exact hK u ((kmem u).mp hu) v ((kmem v).mp hv) ((he u v).mpr h)
    have disj' : ∀ k ∈ K', k ∉ W' := by
      intro k hk hw
      exact Set.disjoint_left.mp disj ((kmem k).mp hk) ((wmem k).mp hw)
    obtain ⟨v, hvW, hvK, h⟩ := extension W' (listed W' hw') K' (listed K' hk') disj'
    exact ⟨v, fun hv => hvW ((wmem v).mpr hv), fun hv => hvK ((kmem v).mpr hv),
      fun k hk hD => h k ((kmem k).mpr hk) ((hd v k).mp hD)⟩

end PEqualNP.Outside.L_meta_732

theorem PEqualNP.Outside.L_meta_732 :
    ∀ (E D : Fin 8 → Fin 8 → Prop),
      (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
          (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
        (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
          (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
      (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
          (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
      (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
      ∀ W K : Set (Fin 8),
        (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
        ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k :=
  PEqualNP.Outside.L_meta_732.transfer
