import Mathlib

theorem PEqualNP.Outside.L_meta_733 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
      (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
      ∀ I : Set (Fin n),
        ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
        ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
          (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
          ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  classical
  intro n G X bip I
  have across {u v : Fin n} (hu : u ∉ X) (e : G.Adj u v) : v ∈ X := by
    by_contra hv
    exact hu ((bip u v e).mpr hv)
  constructor
  · rintro ⟨indep, dominates⟩
    let B : Set (Fin n) := {v | v ∈ I ∧ v ∉ X}
    refine ⟨B, fun _ h => h.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro saturated
        by_contra hyB
        have hyI : y ∉ I := fun h => hyB ⟨h, hy⟩
        obtain ⟨x, hx, e⟩ := dominates y hyI
        obtain ⟨b, hb, eb⟩ := saturated x e
        exact indep x hx b hb.1 eb
      · intro hyB x e
        exact ⟨y, hyB, G.symm e⟩
    · intro v
      constructor
      · intro hvI
        by_cases hv : v ∈ X
        · exact Or.inr ⟨hv, fun b hb => indep v hvI b hb.1⟩
        · exact Or.inl ⟨hvI, hv⟩
      · rintro (h | ⟨hv, avoids⟩)
        · exact h.1
        · by_contra hvI
          obtain ⟨b, hb, e⟩ := dominates v hvI
          exact avoids b ⟨hb, (bip v b e).mp hv⟩ e
  · rintro ⟨B, outside, saturated, memI⟩
    constructor
    · intro u hu v hv e
      rcases (memI u).mp hu with huB | ⟨huX, huFree⟩
      · rcases (memI v).mp hv with hvB | ⟨hvX, hvFree⟩
        · exact outside v hvB (across (outside u huB) e)
        · exact hvFree u huB (G.symm e)
      · rcases (memI v).mp hv with hvB | ⟨hvX, _⟩
        · exact huFree v hvB e
        · exact ((bip u v e).mp huX) hvX
    · intro v hvI
      by_cases hvX : v ∈ X
      · by_contra missing
        apply hvI ((memI v).mpr (Or.inr ⟨hvX, ?_⟩))
        intro b hb e
        exact missing ⟨b, (memI b).mpr (Or.inl hb), e⟩
      · have hvB : v ∉ B := fun h => hvI ((memI v).mpr (Or.inl h))
        have h : ¬ (∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b) :=
          fun covered => hvB ((saturated v hvX).mp covered)
        push_neg at h
        obtain ⟨x, e, hx⟩ := h
        exact ⟨x, (memI x).mpr (Or.inr ⟨across hvX e, hx⟩), e⟩
