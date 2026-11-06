/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CollisionMassDisplays
import NField.Alignment.MobiusReciprocalSquare
import NField.Alignment.GcdLcmCapacity

/-! # Literal convergent series and the earlier logarithmic capacity bound -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondarySeriesConsequences
open scoped Topology
open Filter Asymptotics SecondaryCapacityLedger CollisionRemainderDynamics
  CollisionMassReadout CollisionMassDisplays MobiusReciprocalSquare GcdLcmCapacity

/-- Title: `The coprime Euler series has sum one`. -/
theorem coprime_euler_series :
    HasSum (fun k : ℕ => reducedHarmonicStar k/(k : ℝ)^2) 1 :=
  collisionWeight_hasSum

/-- Title: `The reduced Euler tail is its literal infinite series`. -/
theorem reduced_euler_tail_series (N : ℕ) :
    reducedEulerTailMass N=
      ∑' j : ℕ,reducedHarmonicStar (j+(N+1))/((j+(N+1) : ℕ) : ℝ)^2 :=
  (weight_tail_literal N).symm

/-- Title: `The logarithmic reciprocal-square moment is summable`. -/
theorem logarithmic_reciprocal_square_summable :
    Summable (fun d : ℕ => (1+|Real.log (d : ℝ)|^2)/(d : ℝ)^2) := by
  apply Summable.of_nonneg_of_le
    (f := fun d : ℕ => 25*(d : ℝ)^(-3/2 : ℝ))
  · intro d
    positivity
  · intro d
    by_cases hd : d=0
    · subst d
      norm_num
    · have hl : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
      calc
        _ ≤ (1+Real.log (d : ℝ))^2/(d : ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          rw [sq_abs]
          nlinarith
        _ ≤ _ := one_add_log_sq_div_sq_le_pseries (Nat.pos_of_ne_zero hd)
  · exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 25

/-- Title: `The earlier logarithm-squared bound for the GCD and LCM sum`. -/
theorem gcd_lcm_logarithmic_error :
    (fun N => gcdLcmSquareSum N-3*(N : ℝ)) =O[atTop]
      (fun N => Real.log (2*(N : ℝ))^2) := by
  have h := deficit_isBigO_log_sq.const_mul_left (-3 : ℝ)
  apply h.congr_left
  intro N
  rw [gcdLcmSquareSum_eq_three_continuousCapacity,deficit_eq_capacity]
  ring

end NField.Alignment.SecondarySeriesConsequences
