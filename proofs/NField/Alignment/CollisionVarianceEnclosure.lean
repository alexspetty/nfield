/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTheorem
import NField.Alignment.CollisionCylinderProjection

/-!
# Rational enclosures for the collision potential variance

The dyadic cutoff constant is bounded explicitly by sixteen. An integer
upper bound on the binary logarithm then gives a rational squared L2 error.
A finite rational upper bound on its product with the finite variance
provides an interval for the actual infinite Haar variance.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionVarianceEnclosure

open scoped BigOperators
open Filter CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialCutoff

theorem cutoffRatio_sq : cutoffRatio ^ 2 = (1 / 2 : ℝ) := by
  unfold cutoffRatio
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem cutoffRatio_le_three_quarters : cutoffRatio ≤ (3 / 4 : ℝ) := by
  have hp := cutoffRatio_pos
  have hs := cutoffRatio_sq
  nlinarith

theorem rational_geometric_majorant_hasSum :
    HasSum (fun i : ℕ => ((i : ℝ) + 1) * (3 / 4 : ℝ)^i) 16 := by
  have hnorm : ‖(3 / 4 : ℝ)‖ < 1 := by norm_num
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_norm_lt_one hnorm)
  norm_num at h
  simpa only [add_mul, one_mul] using h

theorem cutoffConstant_le_sixteen : cutoffConstant ≤ 16 := by
  rw [← rational_geometric_majorant_hasSum.tsum_eq]
  apply cutoff_series_summable.tsum_le_tsum _ rational_geometric_majorant_hasSum.summable
  intro i
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ cutoffRatio_pos.le cutoffRatio_le_three_quarters i) (by positivity)

theorem log_twice_le_binary_bound {M b : ℕ} (hM : 1 ≤ M) (hb : 2 * M ≤ 2^b) :
    Real.log (2 * (M : ℝ)) ≤ b := by
  have hpos : (0 : ℝ) < 2 * M := by positivity
  have hle : (2 : ℝ) * M ≤ 2^b := by exact_mod_cast hb
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  exact hlog.trans (by nlinarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg b)])

def rationalSquaredError (M b : ℕ) : ℝ := 256 * ((b : ℝ) + 1)^2 / M

theorem collisionPotential_cutoff_sq_rational {M b : ℕ}
    (hM : 1 ≤ M) (hb : 2 * M ≤ 2^b) :
    ‖collisionPotential - finitePotential collisionWeight M‖^2 ≤ rationalSquaredError M b := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hroot : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr hMR
  have hlog : 0 ≤ 1 + Real.log (2 * (M : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * M by exact_mod_cast (by omega : 1 ≤ 2 * M))
    linarith
  have hn : ‖collisionPotential - finitePotential collisionWeight M‖ ≤
      16 * ((b : ℝ) + 1) / Real.sqrt M := by
    apply (collisionPotential_cutoff_bound hM).trans
    apply div_le_div_of_nonneg_right _ hroot.le
    calc
      _ ≤ 16 * (1 + Real.log (2 * (M : ℝ))) :=
        mul_le_mul_of_nonneg_right cutoffConstant_le_sixteen hlog
      _ ≤ _ := by linarith [log_twice_le_binary_bound hM hb]
  calc
    _ ≤ (16 * ((b : ℝ) + 1) / Real.sqrt M)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by rw [div_pow, Real.sq_sqrt hMR.le]; unfold rationalSquaredError; ring

theorem finiteVariance_le_full (M : ℕ) :
    ‖finitePotential collisionWeight M‖^2 ≤ ‖collisionPotential‖^2 := by
  apply ge_of_tendsto (tendsto_collisionPotential.norm.pow 2)
  filter_upwards [eventually_ge_atTop M] with n hn
  exact finitePotential_norm_sq_monotone hn

theorem collision_variance_rational_enclosure {M b : ℕ} {u : ℝ}
    (hM : 1 ≤ M) (hb : 2 * M ≤ 2^b) (hu : 0 ≤ u)
    (hcross : ‖finitePotential collisionWeight M‖^2 * rationalSquaredError M b ≤ u^2) :
    ‖collisionPotential‖^2 ∈ Set.Icc (‖finitePotential collisionWeight M‖^2)
      (‖finitePotential collisionWeight M‖^2 + 2*u + rationalSquaredError M b) := by
  refine ⟨finiteVariance_le_full M, ?_⟩
  have he := collisionPotential_cutoff_sq_rational hM hb
  have hp := mul_le_mul_of_nonneg_left he (sq_nonneg ‖finitePotential collisionWeight M‖)
  have hprod : ‖finitePotential collisionWeight M‖ *
      ‖collisionPotential - finitePotential collisionWeight M‖ ≤ u := by
    have hn := mul_nonneg (norm_nonneg (finitePotential collisionWeight M))
      (norm_nonneg (collisionPotential - finitePotential collisionWeight M))
    nlinarith
  have hn : ‖collisionPotential‖ ≤ ‖finitePotential collisionWeight M‖ +
      ‖collisionPotential - finitePotential collisionWeight M‖ := by
    calc
      _ = ‖finitePotential collisionWeight M +
          (collisionPotential - finitePotential collisionWeight M)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith

theorem cylinder_cutoff_sq_rational {M b : ℕ} (hM : 1 ≤ M) (hb : 2 * M ≤ 2^b) :
    ‖collisionPotential - CollisionCylinderProjection.cylinderApproximation
      (CollisionOdometerRecurrence.cutoffPeriod M)‖^2 ≤ rationalSquaredError M b := by
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CollisionCylinderProjection.cylinder_cutoff_error_le M) 2).trans
    (collisionPotential_cutoff_sq_rational hM hb)

end NField.Alignment.CollisionVarianceEnclosure
