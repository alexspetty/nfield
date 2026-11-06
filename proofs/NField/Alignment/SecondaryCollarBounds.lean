/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryPrintedBounds
import NField.Alignment.SquareLockCarrierMass

/-! # Actual absolute collar bounds, including the final empty carrier -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryCollarBounds
open scoped BigOperators Classical
open SquareLockCarrierMass PrimeSquareCubicEnergy DedekindFourierMoment CarrierStateSwitching

theorem centered_residue_interval (n k : ℕ) (hk : 0 < k) :
    -(k : ℤ) < 2 * centeredNaturalResidue n k ∧
      2 * centeredNaturalResidue n k ≤ (k : ℤ) := by
  have hr := Nat.mod_lt n hk
  unfold centeredNaturalResidue
  dsimp only
  split_ifs <;> omega

/-- Title: `The exact floor-layer cadence includes the final empty carrier`. -/
theorem slice_re_eq_prefix_layers {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) :
    (modulusKSlice p k).re =
      ∑ h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
        (carrierPrefix p k ((p - 1) / h) : ℝ) := by
  by_cases hstrict : k < p - 1
  · exact modulusKSlice_re_eq_prefixLayers hp hk hstrict
  · have hI : Finset.Ico (k + 1) p = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have hfloor : (p - 1) / (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    have hz : modulusKSlice p k = 0 := by
      unfold modulusKSlice
      split_ifs <;> simp [hI]
    simp [hz, hfloor]

theorem slice_re_le_absolute_collar {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    |(modulusKSlice p k).re| ≤ carrierAbsoluteCollar p k := by
  by_cases hstrict : k < p-1
  · exact abs_modulusKSlice_re_le_carrierAbsoluteCollar hp hk hstrict
  · have hI : Finset.Ico (k+1) p=∅ := Finset.Ico_eq_empty_of_le (by omega)
    have hz : modulusKSlice p k=0 := by
      unfold modulusKSlice
      split_ifs <;> simp [hI]
    rw [hz,Complex.zero_re,abs_zero]
    unfold carrierAbsoluteCollar
    positivity

/-- Title: `The actual small-displacement reservoir is bounded by its collar mass`. -/
theorem small_displacement_reservoir_bound {p : ℕ} (hp : p.Prime) (C : ℕ) :
    (8/(p : ℝ)^2)*|(∑ k ∈ smallDisplacementCarriers p C,modulusKSlice p k).re| ≤
      squareLockCollarMass p C := by
  unfold squareLockCollarMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Complex.re_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
  exact slice_re_le_absolute_collar hp hi.1 (by omega)

theorem absolute_collar_first_moment {p k : ℕ} [NeZero k]
    (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    carrierAbsoluteCollar p k ≤ (((p-1)/(k+1) : ℕ) : ℝ)*dedekindFirstMoment k := by
  unfold carrierAbsoluteCollar
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 ((p-1)/(k+1)),dedekindFirstMoment k := by
      apply Finset.sum_le_sum
      intro h hh
      exact abs_carrierPrefix_le_firstMoment hp hk hkp
    _ = _ := by simp

/-- Title: `Every absolute collar has the carrier's own logarithmic bound`. -/
theorem absolute_collar_own_logarithm {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    carrierAbsoluteCollar p k ≤ (9/4 : ℝ)*(p : ℝ)*Real.log (2*(k : ℝ))^2 := by
  letI : NeZero k := ⟨by omega⟩
  have hfloor : (((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ) ≤ p := by
    exact_mod_cast (Nat.mul_le_mul_left ((p-1)/(k+1)) (Nat.le_succ k)).trans
      ((Nat.div_mul_le_self _ _).trans (Nat.sub_le p 1))
  calc
    _ ≤ (((p-1)/(k+1) : ℕ) : ℝ)*dedekindFirstMoment k := absolute_collar_first_moment hp hk hkp
    _ ≤ (((p-1)/(k+1) : ℕ) : ℝ)*((9/4 : ℝ)*(k : ℝ)*Real.log (2*(k : ℝ))^2) :=
      mul_le_mul_of_nonneg_left (SecondaryPrintedBounds.first_absolute_moment_logarithmic hk) (by positivity)
    _ = (9/4 : ℝ)*((((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ))*Real.log (2*(k : ℝ))^2 := by ring
    _ ≤ _ := by gcongr

end NField.Alignment.SecondaryCollarBounds
