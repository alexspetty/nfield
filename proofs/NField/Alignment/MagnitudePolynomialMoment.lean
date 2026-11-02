/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeLTruncation

/-!
# The finite Dirichlet polynomial behind the fourth moment

The coefficients count the literal ordered pairs in the truncated interval.
Their positivity and divisor bound retain the endpoints. Squaring the actual
truncation is a finite multiplicative convolution, not a supplied identity.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudePolynomialMoment

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.MagnitudeLTruncation
open NField.Alignment.CollisionPeriodicLValue
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.SpectralRepulsion

def productPairs (T u : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 T).product (Finset.Icc 1 T)).filter (fun a => a.1*a.2=u)

noncomputable def coefficient (T u : ℕ) : ℝ :=
  ((productPairs T u).card : ℝ) / u

theorem productPairs_card_le_divisors (T u : ℕ) :
    (productPairs T u).card ≤ u.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro a ha
    obtain ⟨hmem, hprod⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp hmem
    have hpos : 0 < a.1*a.2 := Nat.mul_pos
      (Finset.mem_Icc.mp ha1).1 (Finset.mem_Icc.mp ha2).1
    exact Nat.mem_divisors.mpr ⟨⟨a.2, hprod.symm⟩, by omega⟩
  · intro a ha b hb hab
    obtain ⟨hamem, haprod⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbmem, hbprod⟩ := Finset.mem_filter.mp hb
    have hap : 0 < a.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hamem).1).1
    apply Prod.ext hab
    apply Nat.mul_left_cancel hap
    change a.1 = b.1 at hab
    exact haprod.trans (by simpa only [hab] using hbprod.symm)

theorem coefficient_nonneg (T u : ℕ) : 0 ≤ coefficient T u := by
  unfold coefficient
  positivity

theorem coefficient_le_divisor_weight (T u : ℕ) :
    coefficient T u ≤ (u.divisors.card : ℝ)/u := by
  unfold coefficient
  gcongr
  exact productPairs_card_le_divisors T u

/-- The paper's coefficient is the literal positive ordered-pair count,
with both endpoints included, and is bounded by the divisor weight. -/
theorem coefficient_spec (T u : ℕ) :
    0 ≤ coefficient T u ∧
      coefficient T u = ((productPairs T u).card : ℝ)/u ∧
      coefficient T u ≤ (u.divisors.card : ℝ)/u :=
  ⟨coefficient_nonneg T u, rfl, coefficient_le_divisor_weight T u⟩

theorem product_in_square_interval {T : ℕ} {a : ℕ × ℕ}
    (ha : a ∈ (Finset.Icc 1 T).product (Finset.Icc 1 T)) :
    a.1*a.2 ∈ Finset.Icc 1 (T^2) := by
  obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
  obtain ⟨ha1pos, ha1le⟩ := Finset.mem_Icc.mp ha1
  obtain ⟨ha2pos, ha2le⟩ := Finset.mem_Icc.mp ha2
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.mul_pos ha1pos ha2pos, by simpa [pow_two] using Nat.mul_le_mul ha1le ha2le⟩

/-- The exact coefficient expansion of the square of the literal ordered
Dirichlet truncation, for every character and finite cutoff. -/
theorem ordered_polynomial_square {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℕ) :
    orderedLPartial χ T ^ 2 =
      ∑ u ∈ Finset.Icc 1 (T^2), (coefficient T u : ℂ) * χ (u : ZMod q) := by
  classical
  have hpart : orderedLPartial χ T =
      ∑ n ∈ Finset.Icc 1 T, χ (n : ZMod q)/(n : ℂ) :=
    (positive_interval_sum_eq_range (fun n => χ (n : ZMod q)/(n : ℂ)) T).symm
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (g := fun a : ℕ × ℕ => a.1*a.2)
    (fun a (ha : a ∈ (Finset.Icc 1 T).product (Finset.Icc 1 T)) =>
      product_in_square_interval ha)
    (fun u : ℕ => χ (u : ZMod q)/(u : ℂ))
  calc
    orderedLPartial χ T ^ 2 =
        ∑ a ∈ (Finset.Icc 1 T).product (Finset.Icc 1 T),
          χ ((a.1*a.2 : ℕ) : ZMod q)/((a.1*a.2 : ℕ) : ℂ) := by
      rw [hpart, pow_two, Finset.sum_mul_sum]
      rw [Finset.product_eq_sprod]
      rw [Finset.sum_product (Finset.Icc 1 T) (Finset.Icc 1 T)
        (fun a : ℕ × ℕ => χ ((a.1*a.2 : ℕ) : ZMod q)/((a.1*a.2 : ℕ) : ℂ))]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Nat.cast_mul, map_mul, div_mul_div_comm]
    _ = ∑ u ∈ Finset.Icc 1 (T^2),
        ∑ _a ∈ productPairs T u, χ (u : ZMod q)/(u : ℂ) := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, coefficient, Complex.ofReal_div, Complex.ofReal_natCast]
      ring

theorem modulus_square_polynomial_square {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    orderedLPartial χ (q^2) ^ 2 =
      ∑ u ∈ Finset.Icc 1 (q^4), (coefficient (q^2) u : ℂ) * χ (u : ZMod q) := by
  have hbound : (q^2)^2 = q^4 := by ring
  have h := ordered_polynomial_square χ (q^2)
  rw [hbound] at h
  exact h

theorem residue_character_orthogonality {q : ℕ} [NeZero q] (u v : ℕ) :
    (∑ χ : Character q, star (χ (u : ZMod q)) * χ (v : ZMod q)) =
      if u%q=v%q ∧ u.Coprime q then (q.totient : ℂ) else 0 := by
  classical
  by_cases hu : u.Coprime q
  · have hunit : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime u q).mpr hu
    have hstar (χ : Character q) :
        star (χ (u : ZMod q)) = χ (u : ZMod q)⁻¹ := by
      let U : UnitClass q := ZMod.unitOfCoprime u hu
      have h : star (χ U.val) = χ U.val⁻¹ := by
        calc
          star (χ U.val) = ((χ : MulChar (ZMod q) ℂ)⁻¹) U.val :=
            MulChar.star_apply' _ _
          _ = χ (U⁻¹ : UnitClass q).val := by
            rw [MulChar.inv_apply, Ring.inverse_unit]
          _ = χ U.val⁻¹ := by rw [ZMod.inv_coe_unit]
      simpa only [U, ZMod.coe_unitOfCoprime] using h
    simp_rw [hstar]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit]
    simp only [ZMod.natCast_eq_natCast_iff']
    by_cases huv : u%q=v%q <;> simp [huv, hu]
  · have hunit : ¬ IsUnit (u : ZMod q) := by
      simpa only [ZMod.isUnit_iff_coprime] using hu
    have hz (χ : Character q) : χ (u : ZMod q) = 0 := χ.map_nonunit hunit
    simp [hz, hu]

theorem congruent_coprime_product_iff {q u v : ℕ} (h : u%q=v%q) :
    (u*v).Coprime q ↔ u.Coprime q := by
  have heq : (u : ZMod q) = (v : ZMod q) := (ZMod.natCast_eq_natCast_iff' u v q).mpr h
  have hc : u.Coprime q ↔ v.Coprime q := by
    rw [← ZMod.isUnit_iff_coprime u q, ← ZMod.isUnit_iff_coprime v q, heq]
  rw [Nat.coprime_mul_iff_left, ← hc, and_self]

theorem residue_character_orthogonality_product {q : ℕ} [NeZero q] (u v : ℕ) :
    (∑ χ : Character q, star (χ (u : ZMod q)) * χ (v : ZMod q)) =
      if u%q=v%q ∧ (u*v).Coprime q then (q.totient : ℂ) else 0 := by
  rw [residue_character_orthogonality]
  by_cases h : u%q=v%q
  · simp only [h, true_and, congruent_coprime_product_iff h]
  · simp only [h, false_and, ite_false]

theorem weighted_polynomial_normSq_total {q : ℕ} [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (∑ χ : Character q,
      (Complex.normSq (∑ u ∈ s, (c u : ℂ)*χ (u : ZMod q)) : ℂ)) =
      ∑ u ∈ s, ∑ v ∈ s, (c u : ℂ)*(c v : ℂ) *
        ∑ χ : Character q, star (χ (u : ZMod q))*χ (v : ZMod q) := by
  classical
  have hc (u : ℕ) : star (c u : ℂ) = (c u : ℂ) := Complex.conj_ofReal _
  simp_rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply,
    star_sum, star_mul, hc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem weighted_polynomial_second_moment {q : ℕ} [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℝ) :
    uniformAverage (fun χ : Character q =>
      ‖∑ u ∈ s, (c u : ℂ)*χ (u : ZMod q)‖^2) =
      ∑ u ∈ s, ∑ v ∈ s, if u%q=v%q ∧ (u*v).Coprime q then c u*c v else 0 := by
  classical
  have h := congrArg Complex.re (weighted_polynomial_normSq_total (q := q) s c)
  simp_rw [residue_character_orthogonality_product] at h
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, apply_ite,
    Complex.zero_re, zero_mul, mul_zero, add_zero, sub_zero] at h
  have htotal : (∑ χ : Character q,
      Complex.normSq (∑ u ∈ s, (c u : ℂ)*χ (u : ZMod q))) =
      (q.totient : ℝ) *
        (∑ u ∈ s, ∑ v ∈ s, if u%q=v%q ∧ (u*v).Coprime q then c u*c v else 0) := by
    rw [h]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u%q=v%q ∧ (u*v).Coprime q <;>
      simp [huv, mul_assoc, mul_comm]
  unfold uniformAverage
  rw [character_card_eq_totient]
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [htotal]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hφ, one_mul]

/-- Full-character orthogonality applied to the literal squared truncation. -/
theorem ordered_polynomial_fourth_moment {q : ℕ} [NeZero q] (T : ℕ) :
    uniformAverage (fun χ : Character q => ‖orderedLPartial χ T‖^4) =
      ∑ u ∈ Finset.Icc 1 (T^2),
        ∑ v ∈ Finset.Icc 1 (T^2) with u%q=v%q ∧ (u*v).Coprime q,
          coefficient T u * coefficient T v := by
  classical
  have hf (χ : Character q) : ‖orderedLPartial χ T‖^4 =
      ‖∑ u ∈ Finset.Icc 1 (T^2), (coefficient T u : ℂ)*χ (u : ZMod q)‖^2 := by
    rw [← ordered_polynomial_square, norm_pow]
    ring
  simp_rw [hf]
  rw [weighted_polynomial_second_moment]
  simp only [Finset.sum_filter]

/-- The exact `q^4` residue-pair formula printed in Proposition 10. -/
theorem modulus_square_fourth_moment {q : ℕ} [NeZero q] :
    uniformAverage (fun χ : Character q => ‖orderedLPartial χ (q^2)‖^4) =
      ∑ u ∈ Finset.Icc 1 (q^4),
        ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ (u*v).Coprime q,
          coefficient (q^2) u * coefficient (q^2) v := by
  have hbound : (q^2)^2 = q^4 := by ring
  have h := ordered_polynomial_fourth_moment (q := q) (q^2)
  rw [hbound] at h
  exact h

end NField.Alignment.MagnitudePolynomialMoment
