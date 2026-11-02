/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveOddBoundaryCrossMoment
import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment

/-!
# Full odd-character Bernoulli moments

Odd-character orthogonality gives the complete twisted Bernoulli table on
the unit group. No primitivity or fiber-balance condition is assumed here.
The conjugate character in the manuscript is retained explicitly.
-/

set_option autoImplicit false

namespace NField.Alignment.OddBernoulliMoments

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.PrimeSquareMagnitudeFamily

attribute [local instance] Classical.propDecidable

theorem odd_boundary_cross_expand {m : ℕ} [NeZero m]
    (μ ν : UnitClass m → ℂ) :
    (∑ χ : Character m with χ.Odd,
      star (boundaryFlux μ χ) * boundaryFlux ν χ) =
      ∑ x : UnitClass m, ∑ y : UnitClass m,
        ν x * star (μ y) * oddCharacterKernel x y := by
  classical
  unfold boundaryFlux
  simp_rw [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  unfold oddCharacterKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem odd_boundary_cross {m : ℕ} [NeZero m]
    (μ ν : UnitClass m → ℂ) :
    (∑ χ : Character m with χ.Odd,
      star (boundaryFlux μ χ) * boundaryFlux ν χ) =
      (m.totient : ℂ) / 2 * ∑ x : UnitClass m,
        ν x * (star (μ x) - star (μ (-x))) := by
  classical
  rw [odd_boundary_cross_expand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [oddCharacterKernel_eq]
  calc
    (∑ y : UnitClass m, ν x * star (μ y) *
        ((1 / 2 : ℂ) * m.totient *
          ((if x = y then 1 else 0) - (if -x = y then 1 else 0)))) =
        (m.totient : ℂ) / 2 *
          ((∑ y : UnitClass m, ν x * star (μ y) * (if x = y then 1 else 0)) -
           (∑ y : UnitClass m, ν x * star (μ y) * (if -x = y then 1 else 0))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by simp [mul_sub]

/-- The sign of the twist follows from reindexing by multiplication by `z`. -/
theorem odd_boundary_twist {m : ℕ} [NeZero m]
    (μ : UnitClass m → ℂ) (z : UnitClass m) :
    (∑ χ : Character m with χ.Odd,
      (Complex.normSq (boundaryFlux μ χ) : ℂ) * χ z.val) =
      (m.totient : ℂ) / 2 * ∑ x : UnitClass m,
        μ x * (star (μ (z*x)) - star (μ (-(z*x)))) := by
  classical
  have h := odd_boundary_cross μ (fun x => μ (z⁻¹*x))
  have hflux (χ : Character m) :
      boundaryFlux (fun x => μ (z⁻¹*x)) χ = χ z.val * boundaryFlux μ χ := by
    unfold boundaryFlux
    calc
      (∑ x : UnitClass m, μ (z⁻¹*x) * χ x.val) =
          ∑ x : UnitClass m, μ (z⁻¹*(z*x)) * χ (z*x).val :=
        (Equiv.sum_comp (Equiv.mulLeft z)
          (fun x => μ (z⁻¹*x) * χ x.val)).symm
      _ = χ z.val * ∑ x : UnitClass m, μ x * χ x.val := by
        simp only [inv_mul_cancel_left, Units.val_mul, map_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hspace :
      (∑ x : UnitClass m, μ (z⁻¹*x) * (star (μ x) - star (μ (-x)))) =
        ∑ x : UnitClass m, μ x *
          (star (μ (z*x)) - star (μ (-(z*x)))) := by
    calc
      _ = ∑ x : UnitClass m, μ (z⁻¹*(z*x)) *
          (star (μ (z*x)) - star (μ (-(z*x)))) :=
        (Equiv.sum_comp (Equiv.mulLeft z)
          (fun x => μ (z⁻¹*x) * (star (μ x) - star (μ (-x))))).symm
      _ = _ := by simp only [inv_mul_cancel_left]
  rw [hspace] at h
  simp_rw [hflux] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply]
  ring

theorem bernoulli_flux {q : ℕ} [NeZero q] (χ : Character q) :
    boundaryFlux (fun x : UnitClass q => (x.val.val : ℂ) / q) χ =
      generalizedBernoulliOne χ := by
  unfold boundaryFlux generalizedBernoulliOne
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The full odd-character table, with an arbitrary unit twist. -/
theorem odd_bernoulli_twist {q : ℕ} [NeZero q]
    (z : UnitClass q) :
    (∑ χ : Character q with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ z.val) =
      (q.totient : ℂ) / (2 * (q : ℂ)^2) *
        ∑ x : UnitClass q, (x.val.val : ℂ) * (2 * ((z*x).val.val : ℂ) - q) := by
  classical
  by_cases hq : q = 1
  · subst q
    have hv (x : ZMod 1) : x.val = 0 := by have h := x.val_lt; omega
    simp [generalizedBernoulliOne, hv]
  have hq : 1 < q := by have h := NeZero.ne q; omega
  letI : Fact (1 < q) := ⟨hq⟩
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := odd_boundary_twist (fun x : UnitClass q => (x.val.val : ℂ) / q) z
  simp_rw [bernoulli_flux] at h
  simp only [generalizedBernoulliOne_inv, ← starRingEnd_apply, Complex.normSq_conj]
  rw [h, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hx : (z*x).val ≠ 0 := Units.ne_zero (z*x)
  have hle : (z*x).val.val ≤ q := Nat.le_of_lt (z*x).val.val_lt
  rw [Units.val_neg, ZMod.neg_val, if_neg hx, Nat.cast_sub hle]
  simp only [star_div₀, star_natCast, star_sub]
  field_simp
  ring

/-- The untwisted odd-character table used in the marginal calculation. -/
theorem odd_bernoulli_square {q : ℕ} [NeZero q] :
    (∑ χ : Character q with χ.Odd,
      Complex.normSq (generalizedBernoulliOne χ⁻¹)) =
      (q.totient : ℝ) / (2 * (q : ℝ)^2) *
        ∑ x : UnitClass q, (2 * (x.val.val : ℝ)^2 - q * x.val.val) := by
  have h := odd_bernoulli_twist (1 : UnitClass q)
  simp only [one_mul, Units.val_one, map_one, mul_one] at h
  have hsum : (∑ x : UnitClass q, (x.val.val : ℂ) * (2 * (x.val.val : ℂ) - q)) =
      ∑ x : UnitClass q, (2 * (x.val.val : ℂ)^2 - q * x.val.val) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- The manuscript's literal twist at two; all odd characters are included. -/
theorem odd_bernoulli_twist_two {q : ℕ} [NeZero q]
    (hqodd : Odd q) :
    (∑ χ : Character q with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2) =
      (q.totient : ℂ) / (2 * (q : ℂ)^2) *
        ∑ x : UnitClass q, (x.val.val : ℂ) *
          (2 * (((2*x.val.val)%q : ℕ) : ℂ) - q) := by
  let z : UnitClass q := ZMod.unitOfCoprime 2 hqodd.coprime_two_left
  have hz : z.val = 2 := by simp [z]
  have hval (x : UnitClass q) : (z*x).val.val = (2*x.val.val)%q := by
    calc
      (z*x).val.val = (2*x.val).val := by rw [Units.val_mul, hz]
      _ = ((2*x.val.val : ℕ) : ZMod q).val := by
        rw [Nat.cast_mul, Nat.cast_two, ZMod.natCast_zmod_val]
      _ = _ := ZMod.val_natCast _ _
  simpa only [hz, hval] using odd_bernoulli_twist z

end NField.Alignment.OddBernoulliMoments
