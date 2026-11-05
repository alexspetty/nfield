/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerLawApproximation

/-!
# Bounded Lipschitz testing of empirical joint reset laws

Locally constant approximations have exact orbit limits. The uniform
integer and Haar L1 errors allow passage to each bounded Lipschitz test.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerLawTests

open scoped BigOperators Classical NNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure ProfinitePeriodicTesting CollisionRemainderDynamics
open CollisionMassReadout CollisionBoundaryTesting CollisionPotentialCoboundary
open CollisionResetIntegrability CollisionIntegerJointMoments CollisionIntegerLawApproximation
open CollisionIntegerSingularity

def jointResetPhase (r : ℕ) (h : Fin r → ℕ) (x : Phase) : Fin r → ℝ :=
  fun i => resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x)

def jointPartialPhase (r M : ℕ) (h : Fin r → ℕ) (x : Phase) : Fin r → ℝ :=
  fun i => resetPartial M (CollisionPotentialCoboundary.translate (h i : ℤ) x)

theorem jointResetPhase_aemeasurable (r : ℕ) (h : Fin r → ℕ) :
    AEMeasurable (jointResetPhase r h) phaseHaar := by
  apply aemeasurable_pi_iff.mpr
  intro i
  have hi := ((translate_measurePreserving (h i : ℤ)).integrable_comp
    resetFunction_integrable.aestronglyMeasurable).mpr resetFunction_integrable
  convert! hi.aestronglyMeasurable.aemeasurable using 1

theorem jointPartialPhase_locallyConstant (r M : ℕ) (h : Fin r → ℕ) :
    IsLocallyConstant (jointPartialPhase r M h) := by
  apply locallyConstant_finite_pi
  intro i
  exact (resetPartial_locallyConstant M).comp_continuous (continuous_const.mul continuous_id)

def partialTest (r M : ℕ) (h : Fin r → ℕ) (φ : (Fin r → ℝ) → ℝ) :
    LocallyConstant Phase ℝ :=
  ⟨fun x => φ (jointPartialPhase r M h x), (jointPartialPhase_locallyConstant r M h).comp φ⟩

def lawErrorBound (r : ℕ) (h : Fin r → ℕ) (L : ℝ≥0) (M : ℕ) : ℝ :=
  (L : ℝ)*(∑ i, (1+(h i : ℝ)))*tailMass M

theorem lawErrorBound_tendsto_zero (r : ℕ) (h : Fin r → ℕ) (L : ℝ≥0) :
    Tendsto (lawErrorBound r h L) atTop (nhds 0) := by
  have ht := tailMass_tendsto_zero.const_mul ((L : ℝ)*(∑ i, (1+(h i : ℝ))))
  simp only [mul_zero] at ht
  convert! ht using 1

theorem lipschitz_finite_difference (r : ℕ) {φ : (Fin r → ℝ) → ℝ}
    {L : ℝ≥0} (hφ : LipschitzWith L φ) (v w : Fin r → ℝ) :
    ‖φ v-φ w‖≤(L : ℝ)*∑ i, ‖v i-w i‖ :=
  (hφ.norm_sub_le v w).trans
    (mul_le_mul_of_nonneg_left (finite_pi_norm_le_sum (v-w)) L.coe_nonneg)

theorem testAverage_error_bound (r M N : ℕ) (h : Fin r → ℕ)
    {φ : (Fin r → ℝ) → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ‖orbitAverage N (fun n => φ (jointResetPhase r h (integerPhase n)))-
      orbitAverage N (fun n => partialTest r M h φ (integerPhase n))‖≤
        lawErrorBound r h L M := by
  rw [← orbitAverage_sub]
  calc
    _ ≤ orbitAverage N (fun n => ‖φ (jointResetPhase r h (integerPhase n))-
      φ (jointPartialPhase r M h (integerPhase n))‖) := orbitAverage_norm_bound _ _
    _ ≤ orbitAverage N (fun n => (L : ℝ)*∑ i,
      ‖jointResetPhase r h (integerPhase n) i-jointPartialPhase r M h (integerPhase n) i‖) :=
        orbitAverage_mono _ (fun n => lipschitz_finite_difference r hφ _ _)
    _ = (L : ℝ)*∑ i, orbitAverage N (fun n =>
      ‖resetFunction (integerPhase (n+h i : ℕ))-resetPartial M (integerPhase (n+h i : ℕ))‖) := by
        rw [orbitAverage_const_mul, orbitAverage_finsetSum]
        simp only [jointResetPhase, jointPartialPhase, translate_integerPhase]
    _ ≤ (L : ℝ)*∑ i, (1+(h i : ℝ))*tailMass M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        resetPartial_integer_L1_error M (h i) N)) L.coe_nonneg
    _ = lawErrorBound r h L M := by rw [← Finset.sum_mul, lawErrorBound, mul_assoc]

theorem bounded_test_integrable (r : ℕ) (h : Fin r → ℕ) {φ : (Fin r → ℝ) → ℝ}
    (hc : Continuous φ) (hb : ∃ C : ℝ, ∀ v w, dist (φ v) (φ w)≤C) :
    Integrable (fun x => φ (jointResetPhase r h x)) phaseHaar := by
  obtain ⟨C, hC⟩ := hb
  apply (integrable_const (C+‖φ 0‖)).mono'
    (hc.comp_aestronglyMeasurable (jointResetPhase_aemeasurable r h).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  have hb := hC (jointResetPhase r h x) 0
  rw [dist_eq_norm] at hb
  have ht := norm_add_le (φ (jointResetPhase r h x)-φ 0) (φ 0)
  rw [sub_add_cancel] at ht
  linarith

theorem shifted_error_integrable (M h : ℕ) :
    Integrable (fun x => ‖resetFunction (CollisionPotentialCoboundary.translate (h : ℤ) x)-
      resetPartial M (CollisionPotentialCoboundary.translate (h : ℤ) x)‖) phaseHaar := by
  have hbase := (resetFunction_integrable.sub (resetPartial_integrable M)).norm
  have hi := ((translate_measurePreserving (h : ℤ)).integrable_comp
    hbase.aestronglyMeasurable).mpr hbase
  convert! hi using 1

theorem testIntegral_error_bound (r M : ℕ) (h : Fin r → ℕ)
    {φ : (Fin r → ℝ) → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hb : ∃ C : ℝ, ∀ v w, dist (φ v) (φ w)≤C) :
    ‖(∫ x, φ (jointResetPhase r h x) ∂phaseHaar)-
      (∫ x, partialTest r M h φ x ∂phaseHaar)‖≤lawErrorBound r h L M := by
  have hi := bounded_test_integrable r h hφ.continuous hb
  have hj : Integrable (fun x => partialTest r M h φ x) phaseHaar := by
    have hj := continuous_phase_integrable ((partialTest r M h φ : LocallyConstant Phase ℝ) : C(Phase, ℝ))
    convert! hj using 1
  have hδ := integrable_finsetSum Finset.univ (fun i _ => shifted_error_integrable M (h i))
  rw [← integral_sub hi hj]
  calc
    _ ≤ ∫ x, ‖φ (jointResetPhase r h x)-φ (jointPartialPhase r M h x)‖ ∂phaseHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, (L : ℝ)*∑ i, ‖resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x)-
      resetPartial M (CollisionPotentialCoboundary.translate (h i : ℤ) x)‖ ∂phaseHaar := by
        exact integral_mono_ae (hi.sub hj).norm (hδ.const_mul (L : ℝ))
          (Eventually.of_forall (fun x => lipschitz_finite_difference r hφ _ _))
    _ = (L : ℝ)*∑ _i : Fin r, tailMass M := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => shifted_error_integrable M (h i))]
      simp only [resetPartial_shifted_L1_error]
    _ ≤ (L : ℝ)*∑ i, (1+(h i : ℝ))*tailMass M := by
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply Finset.sum_le_sum
      intro i _
      nlinarith [tailMass_nonneg M, Nat.cast_nonneg (α := ℝ) (h i)]
    _ = lawErrorBound r h L M := by rw [← Finset.sum_mul, lawErrorBound, mul_assoc]

theorem joint_reset_bounded_lipschitz_tendsto (r : ℕ) (h : Fin r → ℕ)
    {φ : (Fin r → ℝ) → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hb : ∃ C : ℝ, ∀ v w, dist (φ v) (φ w)≤C) :
    Tendsto (fun N => orbitAverage N (fun n => φ (jointResetPhase r h (integerPhase n))))
      atTop (nhds (∫ x, φ (jointResetPhase r h x) ∂phaseHaar)) := by
  exact tendsto_of_uniform_approximations _
    (fun M N => orbitAverage N (fun n => partialTest r M h φ (integerPhase n))) _
    (fun M => ∫ x, partialTest r M h φ x ∂phaseHaar) (lawErrorBound r h L)
    (lawErrorBound_tendsto_zero r h L)
    (fun M => locallyConstant_orbit_tendsto (partialTest r M h φ))
    (fun M N => testAverage_error_bound r M N h hφ)
    (fun M => testIntegral_error_bound r M h hφ hb)

end NField.Alignment.CollisionIntegerLawTests
