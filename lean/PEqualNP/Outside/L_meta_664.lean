import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664

open QuotientAddGroup

private def q {F : Type} [Field F] (b : F) (v : F × F) : F :=
  v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

private theorem q_eq_zero {F : Type} [Field F] {b : F}
    (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) {v : F × F} (hv : q b v = 0) :
    v = 0 := by
  rcases v with ⟨x, y⟩
  by_cases hy : y = 0
  · subst y
    have hx : x ^ 2 = 0 := by simpa [q] using hv
    rw [pow_two, mul_eq_zero] at hx
    simp [hx.elim id id]
  · exfalso
    apply hb (x / y)
    calc
      (x / y) ^ 2 + b * (x / y) + 1 = q b (x, y) / y ^ 2 := by
        simp only [q]
        field_simp
        <;> ring
      _ = 0 := by rw [hv, zero_div]

private theorem mk_zero {F : Type} [Field F] (B : AddSubgroup F) (x : F) :
    mk' B x = 0 ↔ x ∈ B := by
  change x ∈ (mk' B).ker ↔ x ∈ B
  rw [ker_mk']

private theorem count_fiber {F : Type} [Field F] [Fintype F]
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (f : F →+ F) (e t0 : F)
    (h0 : f t0 + e ∈ A) (hs : Function.Surjective ((mk' A).comp f)) :
    (Finset.univ.filter (fun t => f t + e ∈ A)).card = Nat.card A := by
  classical
  let g := (mk' A).comp f
  have same (t : F) : f t + e ∈ A ↔ g t = g t0 := by
    rw [← mk_zero A, map_add]
    have hzero : g t0 + mk' A e = 0 := by
      simpa only [g, AddMonoidHom.comp_apply, ← map_add] using (mk_zero A _).mpr h0
    change g t + mk' A e = 0 ↔ g t = g t0
    rw [← hzero, add_left_inj]
  let shift : {t : F // f t + e ∈ A} ≃ g.ker :=
    { toFun := fun t => ⟨t - t0, by
        change g (t - t0) = 0
        rw [map_sub, (same t).mp t.property, sub_self]⟩
      invFun := fun t => ⟨t + t0, (same _).mpr (by
        have ht : g t = 0 := t.property
        rw [map_add, ht, zero_add])⟩
      left_inv := fun t => Subtype.ext (sub_add_cancel (t : F) t0)
      right_inv := fun t => Subtype.ext (add_sub_cancel_right (t : F) t0) }
  have hker : Nat.card g.ker = Nat.card A := by
    have h₁ := AddSubgroup.card_ker_mul_card_of_surjective (f := g) hs
    have h₂ := A.card_eq_card_quotient_mul_card_addSubgroup
    have hp : 0 < Nat.card (F ⧸ A) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp (h₁.trans (h₂.trans (Nat.mul_comm _ _)))
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr shift).trans hker

private theorem count_line {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F) (hd : d ≠ 0) :
    ((Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = 0 ∨
      (Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = Nat.card A) ∧
    (p = 0 → (Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = Nat.card A) := by
  classical
  let a := q b d
  let c := b * (p.1 * d.2 + d.1 * p.2)
  let e := q b p
  have ha : a ≠ 0 := fun h => hd (q_eq_zero hb h)
  have htwo : (2 : F) = 0 := CharP.ofNat_eq_zero F 2
  let f : F →+ F :=
    { toFun := fun t => a * t ^ 2 + c * t
      map_zero' := by simp
      map_add' := fun x y => by
        change a * (x + y) ^ 2 + c * (x + y) =
          a * x ^ 2 + c * x + (a * y ^ 2 + c * y)
        linear_combination (a * x * y) * htwo }
  have line (t : F) : q b (p + t • d) = f t + e := by
    change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) +
      (p.2 + t * d.2) ^ 2 = a * t ^ 2 + c * t + e
    dsimp [a, c, e, q]
    linear_combination (p.1 * t * d.1 + p.2 * t * d.2) * htwo
  simp only [line]
  have count (t0 : F) (ht0 : f t0 + e ∈ A) :
      (Finset.univ.filter (fun t => f t + e ∈ A)).card = Nat.card A := by
    apply count_fiber A f e t0 ht0
    by_cases hc : c = 0
    · have hf : Function.Injective f := by
        intro x y hxy
        have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        change a * (x - y) ^ 2 + c * (x - y) = 0 at hz
        rw [hc, zero_mul, add_zero] at hz
        have hs := (mul_eq_zero.mp hz).resolve_left ha
        rw [pow_two, mul_eq_zero] at hs
        exact sub_eq_zero.mp (hs.elim id id)
      exact (mk'_surjective A).comp ((Finite.injective_iff_surjective).mp hf)
    · let k := -c / a
      have hk : k ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc) ha
      have roots (t : F) : f t = 0 ↔ t = 0 ∨ t = k := by
        change a * t ^ 2 + c * t = 0 ↔ _
        rw [show a * t ^ 2 + c * t = t * (a * t + c) by ring, mul_eq_zero]
        congr 1
        rw [add_eq_zero_iff_eq_neg, eq_div_iff ha, mul_comm]
      have hker : Nat.card f.ker = 2 := by
        apply (Nat.card_eq_two_iff' (0 : f.ker)).mpr
        refine ⟨⟨k, (roots k).mpr (Or.inr rfl)⟩, ?_, ?_⟩
        · exact fun h => hk (congrArg Subtype.val h)
        · intro t ht
          apply Subtype.ext
          exact ((roots t).mp t.property).resolve_left (fun h => ht (Subtype.ext h))
      have hi : f.range.index = 2 := by
        have h₁ := AddSubgroup.card_ker_mul_card_range f
        rw [hker] at h₁
        exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card f.range)
          (f.range.index_mul_card.trans h₁.symm)
      have he : e ∉ f.range := by
        rintro ⟨t, ht⟩
        have hq : q b (p + (-t) • d) = 0 := by
          rw [line, map_neg, ht, neg_add_cancel]
        have hvec := q_eq_zero hb hq
        have hx : p.1 = -((-t) * d.1) :=
          eq_neg_of_add_eq_zero_left (congrArg Prod.fst hvec)
        have hy : p.2 = -((-t) * d.2) :=
          eq_neg_of_add_eq_zero_left (congrArg Prod.snd hvec)
        apply hc
        dsimp [c]
        rw [hx, hy]
        linear_combination (b * t * d.1 * d.2) * htwo
      let a0 := f t0 + e
      let r := mk' f.range
      have hra : r a0 = r e := by
        change r (f t0 + e) = r e
        rw [map_add, (mk_zero f.range _).mpr ⟨t0, rfl⟩, zero_add]
      have hu := (Nat.card_eq_two_iff' (0 : F ⧸ f.range)).mp
        (f.range.index_eq_card.symm.trans hi)
      have hunique : ∀ x : F ⧸ f.range, x ≠ 0 → x = r e := by
        obtain ⟨z, hz, huniq⟩ := hu
        have hre : r e ≠ 0 := fun h => he ((mk_zero f.range e).mp h)
        intro x hx
        exact (huniq x hx).trans (huniq (r e) hre).symm
      intro x
      obtain ⟨y, rfl⟩ := mk'_surjective A x
      by_cases hy : r y = 0
      · obtain ⟨t, ht⟩ := (mk_zero f.range y).mp hy
        exact ⟨t, by change mk' A (f t) = mk' A y; rw [ht]⟩
      · have hsub : r (y - a0) = 0 := by
          rw [map_sub, hunique (r y) hy, hra, sub_self]
        obtain ⟨t, ht⟩ := (mk_zero f.range _).mp hsub
        have hya : mk' A a0 = 0 := (mk_zero A _).mpr ht0
        exact ⟨t, by change mk' A (f t) = mk' A y; rw [ht, map_sub, hya, sub_zero]⟩
  constructor
  · by_cases h : ∃ t, f t + e ∈ A
    · obtain ⟨t, ht⟩ := h
      exact Or.inr (count t ht)
    · left
      apply Finset.card_eq_zero.mpr
      ext t
      have ht : f t + e ∉ A := fun hmem => h ⟨t, hmem⟩
      simp [ht]
  · intro hp
    apply count 0
    have he : e = 0 := by simp [e, hp, q]
    simp [he]

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  exact PEqualNP.Outside.L_meta_664.count_line b hb A p d hd
