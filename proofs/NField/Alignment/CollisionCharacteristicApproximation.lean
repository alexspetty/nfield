/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacteristicCycles
import NField.Alignment.CollisionL1Testing

/-!
# Quantitative characteristic-function approximation

The finite averages use the literal full lcm period. The imaginary
exponential error is bounded by abs(t) times the actual L1 cutoff error,
which in turn is bounded by the proved L2 error.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCharacteristicApproximation

open scoped Classical ENNReal
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionDistributionApproximation CollisionPotentialCutoff
open CollisionPotentialMoments CollisionL1Testing CollisionCharacteristicLaw
open CollisionCharacteristicCycles CollisionOdometerRecurrence

theorem cutoff_error_L1_le_L2 (M : ℕ) :
    (∫ x, |potentialMap collisionWeight M x-collisionPotential x| ∂phaseHaar) ≤
      ‖collisionPotential-finitePotential collisionWeight M‖ := by
  calc
    _ = ‖lowerL2Linear (finitePotential collisionWeight M-collisionPotential)‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [cutoff_error_vector_coe M] with x hx
      change |potentialMap collisionWeight M x-collisionPotential x|=
        ‖(finitePotential collisionWeight M-collisionPotential) x‖
      rw [hx,Real.norm_eq_abs]
    _ ≤ ‖finitePotential collisionWeight M-collisionPotential‖ := lowerL2Linear_norm _
    _ = _ := norm_sub_rev _ _

theorem characteristic_cutoff_error_L2 (M : ℕ) (t : ℝ) :
    ‖potentialCharacteristic t-cutoffCharacteristic M t‖ ≤
      |t| * ‖collisionPotential-finitePotential collisionWeight M‖ := by
  have hF := memLp_one_iff_integrable.mp (cutoff_memLp_finite M 1 (by simp))
  have hG := memLp_one_iff_integrable.mp (potential_memLp_finite 1 (by simp))
  rw [norm_sub_rev,potentialCharacteristic_integral,cutoffCharacteristic_integral]
  exact (characteristic_difference_L1 (potentialMap collisionWeight M) collisionPotential hF hG t).trans
    (mul_le_mul_of_nonneg_left (cutoff_error_L1_le_L2 M) (abs_nonneg t))

theorem cutoffCharacteristic_tendsto (t : ℝ) :
    Tendsto (fun M => cutoffCharacteristic M t) atTop (nhds (potentialCharacteristic t)) := by
  have hY : Tendsto (fun M => ‖collisionPotential-finitePotential collisionWeight M‖)
      atTop (nhds 0) := by
    simpa only [sub_self,norm_zero] using
      ((tendsto_const_nhds (x := collisionPotential)).sub tendsto_collisionPotential).norm
  have h := squeeze_zero (fun M => norm_nonneg (cutoffCharacteristic M t-potentialCharacteristic t))
    (fun M => by simpa only [norm_sub_rev] using characteristic_cutoff_error_L2 M t)
    (by simpa only [mul_zero] using hY.const_mul |t|)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h

theorem characteristic_uniform_error : ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M → ∀ t : ℝ,
    ‖potentialCharacteristic t-cutoffCharacteristic M t‖ ≤
      K * |t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ) := by
  let C : ℝ := cutoffConstant*(1+1/Real.log 2)
  have hC : 0 ≤ C := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_nonneg cutoffConstant_nonneg (by positivity)
  refine ⟨C+1,by positivity,?_⟩
  intro M hM t
  have hlog : 0 ≤ Real.log (2*(M : ℝ)) := Real.log_nonneg (by
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith)
  calc
    _ ≤ |t| * ‖collisionPotential-finitePotential collisionWeight M‖ :=
      characteristic_cutoff_error_L2 M t
    _ ≤ |t| * (C*Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (cutoff_norm_log_uniform hM) (abs_nonneg t)
    _ ≤ (C+1) * |t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ) := by
      have hnon : 0 ≤ |t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ) := by positivity
      calc
        _ = C*(|t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ)) := by ring
        _ ≤ (C+1)*(|t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) hnon
        _ = _ := by ring

theorem characteristic_function_approximation :
    (∀ t : ℝ, potentialCharacteristic t=
      ∫ x, Complex.exp (((t*collisionPotential x : ℝ) : ℂ)*Complex.I) ∂phaseHaar) ∧
    (∀ t : ℝ, Tendsto (fun M =>
      (1/(cutoffPeriod M : ℂ))*∑ a ∈ Finset.range (cutoffPeriod M),
        Complex.exp (((t*finiteAge collisionWeight M a : ℝ) : ℂ)*Complex.I))
      atTop (nhds (potentialCharacteristic t))) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M → ∀ t : ℝ,
      ‖potentialCharacteristic t-cutoffCharacteristic M t‖ ≤
        K * |t| * Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ)) ∧
    (∀ t : ℝ, (potentialCharacteristic t).im=0) ∧
    (∀ t : ℝ, potentialCharacteristic (-t)=potentialCharacteristic t) ∧
    ContDiff ℝ (⊤ : ℕ∞) potentialCharacteristic := by
  exact ⟨potentialCharacteristic_integral,cutoffCharacteristic_tendsto,characteristic_uniform_error,
    potentialCharacteristic_real,potentialCharacteristic_even,potentialCharacteristic_smooth⟩

end NField.Alignment.CollisionCharacteristicApproximation
