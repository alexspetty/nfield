/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialRecovery

/-!
# L1 comparison and bounded tests on the actual profinite Haar space

The inclusion from Haar L2 to Haar L1 is contractive. Pairing against a
continuous test is a bounded functional on L1 and agrees with the Haar
Hilbert pairing. These maps retain the actual almost-everywhere functions.
-/

noncomputable section

namespace NField.Alignment.CollisionL1Testing

open scoped BigOperators ENNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence

abbrev HaarL1 := Lp ℝ 1 phaseHaar

def lowerL2Linear : HaarL2 →ₗ[ℝ] HaarL1 :=
  Submodule.inclusion (show Lp.LpSubmodule ℝ ℝ 2 phaseHaar ≤ Lp.LpSubmodule ℝ ℝ 1 phaseHaar from
    Lp.antitone (by norm_num))

@[simp] theorem lowerL2Linear_coe (f : HaarL2) : (lowerL2Linear f : Phase → ℝ) = f := rfl

theorem lowerL2Linear_norm (f : HaarL2) : ‖lowerL2Linear f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, lowerL2Linear_coe]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable f))

def lowerL2 : HaarL2 →L[ℝ] HaarL1 :=
  lowerL2Linear.mkContinuous 1 (fun f => by simpa only [one_mul] using lowerL2Linear_norm f)

@[simp] theorem lowerL2_coe (f : HaarL2) : (lowerL2 f : Phase → ℝ) = f := rfl

theorem continuous_test_integrable (φ : C(Phase, ℝ)) (f : HaarL1) :
    Integrable (fun x => f x * φ x) phaseHaar := by
  exact (memLp_one_iff_integrable.mp (Lp.memLp f)).mul_bdd
    φ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall φ.norm_coe_le_norm)

def continuousTestLinear (φ : C(Phase, ℝ)) : HaarL1 →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x * φ x ∂phaseHaar
  map_add' f g := by
    calc
      _ = ∫ x, f x * φ x + g x * φ x ∂phaseHaar := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [Pi.add_apply] at hx
        rw [hx, add_mul]
      _ = _ := integral_add (continuous_test_integrable φ f) (continuous_test_integrable φ g)
  map_smul' c f := by
    calc
      _ = ∫ x, c * (f x * φ x) ∂phaseHaar := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [Pi.smul_apply, smul_eq_mul] at hx
        rw [hx, mul_assoc]
      _ = _ := by rw [integral_const_mul]; rfl

theorem continuousTestLinear_bound (φ : C(Phase, ℝ)) (f : HaarL1) :
    ‖continuousTestLinear φ f‖ ≤ ‖φ‖ * ‖f‖ := by
  calc
    _ ≤ ∫ x, ‖f x * φ x‖ ∂phaseHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ‖ * ‖f x‖ ∂phaseHaar := by
      apply integral_mono_ae (continuous_test_integrable φ f).norm
        ((memLp_one_iff_integrable.mp (Lp.memLp f)).norm.const_mul ‖φ‖)
      filter_upwards [] with x
      rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm x) (norm_nonneg (f x))
    _ = _ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]

def continuousTest (φ : C(Phase, ℝ)) : HaarL1 →L[ℝ] ℝ :=
  (continuousTestLinear φ).mkContinuous ‖φ‖ (continuousTestLinear_bound φ)

theorem continuousTest_eq_integral (φ : C(Phase, ℝ)) (f : HaarL1) :
    continuousTest φ f = ∫ x, f x * φ x ∂phaseHaar := rfl

theorem continuousTest_lowerL2 (φ : C(Phase, ℝ)) (f : HaarL2) :
    continuousTest φ (lowerL2 f) = inner ℝ f (ContinuousMap.toLp 2 phaseHaar ℝ φ) := by
  rw [continuousTest_eq_integral, lowerL2_coe, L2.inner_def]
  apply integral_congr_ae
  have ht := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar φ
  filter_upwards [ht] with x hx
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx]
  ring

end NField.Alignment.CollisionL1Testing
