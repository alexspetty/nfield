/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentLocalBounds

/-!
# Quantitative losses from finite prime exponents

These estimates compare the actual finite local factors and logarithmic
averages with their limiting values. No limit is substituted for a finite
factor. The estimates hold for every real p >= 2 and every natural v.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLocalFactorLosses

open CollisionResetLocalFactors CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

theorem reciprocal_predecessor_bound {p : ℝ} (hp : 2 ≤ p) : 1/(p-1) ≤ 2/p := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  linarith

theorem alignment_gap_constant_bound {p : ℝ} (hp : 2 ≤ p) :
    (p^2+p+1)/((p-1)*(p+1)^2) ≤ 2/p := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < (p-1)*(p+1)^2 := mul_pos (by linarith) (sq_pos_of_pos (by linarith))
  apply (div_le_div_iff₀ hden hp0).mpr
  nlinarith [mul_nonneg (show 0 ≤ p-2 by linarith) (show 0 ≤ p^2+3*p+1 by positivity)]

theorem resetPrimeAverage_loss_bound {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    0 ≤ 1/(p-1)-resetPrimeAverage p v ∧
      1/(p-1)-resetPrimeAverage p v ≤ ((v : ℝ)+2)*(p⁻¹)^(v+1) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hA := (resetPrimeFactor_bounds hp1 v).1
  have hA0 : resetPrimeFactor p v ≠ 0 := ne_of_gt (by linarith)
  have hgap : 1/(p-1)-resetPrimeAverage p v=
      ((p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹))/resetPrimeFactor p v := by
    rw [← resetPrimeNumerator_gap hp1 v]
    unfold resetPrimeAverage
    field_simp
  constructor
  · exact sub_nonneg.mpr (resetPrimeAverage_bounds hp1 v).2
  · rw [hgap]
    calc
      _ ≤ (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹) := div_le_self (by positivity) hA
      _ ≤ (p⁻¹)^v*((v : ℝ)*p⁻¹+2/p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add le_rfl (by simpa only [one_div] using reciprocal_predecessor_bound hp)
      _ = _ := by rw [pow_succ]; ring

theorem alignmentPrimeAverage_loss_bound {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    0 ≤ 1/(p-1)-alignmentPrimeAverage p v ∧
      1/(p-1)-alignmentPrimeAverage p v ≤ ((v : ℝ)+2)*(p⁻¹)^(v+1) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hK := (alignmentPrimeFactor_bounds hp1 v).1
  have hK0 : alignmentPrimeFactor p v ≠ 0 := ne_of_gt (by linarith)
  have hgap : 1/(p-1)-alignmentPrimeAverage p v=
      ((p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2)))/alignmentPrimeFactor p v := by
    rw [← alignmentPrimeNumerator_gap hp1 v]
    unfold alignmentPrimeAverage
    field_simp
  constructor
  · exact sub_nonneg.mpr (alignmentPrimeAverage_bounds hp1 v).2
  · rw [hgap]
    calc
      _ ≤ (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2)) :=
        div_le_self (by positivity) hK
      _ ≤ (p⁻¹)^v*((v : ℝ)/p+2/p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add _ (alignment_gap_constant_bound hp)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp0 (by linarith)
      _ = _ := by rw [pow_succ]; ring

theorem resetPrimeFactor_relative_loss_bound {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    0 ≤ ((1+p⁻¹)-resetPrimeFactor p v)/(1+p⁻¹) ∧
      ((1+p⁻¹)-resetPrimeFactor p v)/(1+p⁻¹) ≤ (p⁻¹)^(v+1) := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 ≤ 1+p⁻¹ := by linarith [inv_nonneg.mpr hp0.le]
  have he : ((1+p⁻¹)-resetPrimeFactor p v)/(1+p⁻¹)=(p⁻¹)^(v+1)/(1+p⁻¹) := by
    unfold resetPrimeFactor
    ring
  rw [he]
  exact ⟨by positivity,div_le_self (by positivity) h1⟩

theorem alignmentPrimeFactor_relative_loss_bound {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    0 ≤ ((1+p⁻¹)-alignmentPrimeFactor p v)/(1+p⁻¹) ∧
      ((1+p⁻¹)-alignmentPrimeFactor p v)/(1+p⁻¹) ≤ (p⁻¹)^(v+1) := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 ≤ 1+p⁻¹ := by linarith [inv_nonneg.mpr hp0.le]
  have he : ((1+p⁻¹)-alignmentPrimeFactor p v)/(1+p⁻¹)=
      ((p⁻¹)^v/(p+1))/(1+p⁻¹) := by unfold alignmentPrimeFactor; ring
  rw [he]
  constructor
  · positivity
  · calc
      _ ≤ (p⁻¹)^v/(p+1) := div_le_self (by positivity) h1
      _ ≤ (p⁻¹)^v/p := div_le_div_of_nonneg_left (by positivity) hp0 (by linarith)
      _ = _ := by rw [pow_succ]; ring

end NField.Alignment.CollisionLocalFactorLosses
