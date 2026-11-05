/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionExponentialMoments
import NField.Alignment.CollisionRootTails
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Exponential integrability and finite moments of the actual potential
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialMoments

open scoped Classical ENNReal
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionExponentialMoments CollisionRootTails

theorem potential_root_aemeasurable :
    AEMeasurable (fun x => Real.sqrt |collisionPotential x|) phaseHaar :=
  (Lp.aestronglyMeasurable collisionPotential).aemeasurable.abs.sqrt

theorem cutoff_root_aemeasurable (M : ℕ) :
    AEMeasurable (fun x => Real.sqrt |potentialMap collisionWeight M x|) phaseHaar :=
  (potentialMap collisionWeight M).continuous.abs.sqrt.measurable.aemeasurable

theorem potential_exponential_moments {c : ℝ} (hcπ : c < Real.pi) :
    ∃ B : ℝ, 0 < B ∧
      (Integrable (fun x => Real.exp (c*Real.sqrt |collisionPotential x|)) phaseHaar ∧
        (∫ x, Real.exp (c*Real.sqrt |collisionPotential x|) ∂phaseHaar) ≤ B) ∧
      (∀ M : ℕ, Integrable (fun x => Real.exp (c*Real.sqrt |potentialMap collisionWeight M x|)) phaseHaar ∧
        (∫ x, Real.exp (c*Real.sqrt |potentialMap collisionWeight M x|) ∂phaseHaar) ≤ B) := by
  by_cases hc : 0 < c
  · let d : ℝ := (c+Real.pi)/2
    have hd : 0 < d := by dsimp [d]; linarith [Real.pi_pos]
    have hdπ : d < Real.pi := by dsimp [d]; linarith
    have hcd : c < d := by dsimp [d]; linarith
    obtain ⟨K,hK,htail⟩ := potential_root_tails hd hdπ
    refine ⟨1+K*c/(d-c),by positivity,?_,?_⟩
    · exact exponential_moment_of_tail phaseHaar (fun x => Real.sqrt |collisionPotential x|)
        potential_root_aemeasurable (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))
        hK.le hc hcd (fun t ht => (htail t ht).1)
    · intro M
      exact exponential_moment_of_tail phaseHaar (fun x => Real.sqrt |potentialMap collisionWeight M x|)
        (cutoff_root_aemeasurable M) (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))
        hK.le hc hcd (fun t ht => (htail t ht).2 M)
  · refine ⟨1,by norm_num,?_,?_⟩
    · exact exponential_moment_nonpositive phaseHaar (fun x => Real.sqrt |collisionPotential x|)
        potential_root_aemeasurable (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))
        (le_of_not_gt hc)
    · intro M
      exact exponential_moment_nonpositive phaseHaar (fun x => Real.sqrt |potentialMap collisionWeight M x|)
        (cutoff_root_aemeasurable M) (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))
        (le_of_not_gt hc)

theorem abs_root_rpow (x : ℝ) (r : ℝ) : |Real.sqrt (|x|)| ^ (2*r)=|x|^r := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

theorem power_integrable_of_root_exponential {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (F : Ω → ℝ) {t r : ℝ} (ht : t ≠ 0) (hr : 0 ≤ r)
    (hp : Integrable (fun x => Real.exp (t*Real.sqrt |F x|)) μ)
    (hn : Integrable (fun x => Real.exp (-t*Real.sqrt |F x|)) μ) :
    Integrable (fun x => |F x|^r) μ := by
  have hi := ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul ht hp hn
    (show 0 ≤ 2*r by linarith)
  simpa only [abs_root_rpow] using hi

theorem potential_finite_moments {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun x => |collisionPotential x|^r) phaseHaar ∧
      ∀ M : ℕ, Integrable (fun x => |potentialMap collisionWeight M x|^r) phaseHaar := by
  have ht : Real.pi/2 ≠ 0 := by positivity
  obtain ⟨Bp,hBp,hYp,hMp⟩ := potential_exponential_moments (c := Real.pi/2) (by linarith [Real.pi_pos])
  obtain ⟨Bn,hBn,hYn,hMn⟩ := potential_exponential_moments (c := -(Real.pi/2)) (by linarith [Real.pi_pos])
  exact ⟨power_integrable_of_root_exponential collisionPotential ht hr hYp.1 hYn.1,
    fun M => power_integrable_of_root_exponential (potentialMap collisionWeight M) ht hr
      (hMp M).1 (hMn M).1⟩

theorem potential_memLp_finite (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp collisionPotential p phaseHaar := by
  by_cases hp0 : p=0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr (Lp.aestronglyMeasurable collisionPotential)
  apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable collisionPotential) hp0 hp).mp
  simpa only [Real.norm_eq_abs] using (potential_finite_moments (ENNReal.toReal_nonneg)).1

theorem cutoff_memLp_finite (M : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (potentialMap collisionWeight M) p phaseHaar := by
  have hm : AEStronglyMeasurable (potentialMap collisionWeight M) phaseHaar :=
    (potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable
  by_cases hp0 : p=0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr hm
  apply (integrable_norm_rpow_iff hm hp0 hp).mp
  simpa only [Real.norm_eq_abs] using (potential_finite_moments (ENNReal.toReal_nonneg)).2 M

end NField.Alignment.CollisionPotentialMoments
