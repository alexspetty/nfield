/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperClosedMomentRecursion

/-!
# The actual critical Euler-product low-moment saving

The proved event estimates close the normalized recursion uniformly in
the exponent. Undoing normalization and substituting x=P^exp(1) gives
the critical three-quarter moment bound for the literal unitEnergy.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperCriticalLowMoment
open Filter MeasureTheory SteinhausMoment HarperPrimeBlocks HarperFrequencyIntervals
  HarperNormalizedEnergy HarperMomentRecursion HarperRecursionWeights
  HarperClosedMomentRecursion HarperReverseGrid

theorem actual_normalized_moment_bound :
    ∃ K H : ℝ, 0 < K ∧ 0 < H ∧ ∀ᶠ x : ℝ in atTop,
      1 < sourceCutoff x ∧ 0 < Real.sqrt (Real.log (Real.log x)) ∧
      ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 →
        normalizedMoment (sourceCutoff x) K q ≤ H/(momentWeight (Real.sqrt (Real.log (Real.log x))) q)^q := by
  obtain ⟨K,C,D,hK,hC,hD,hbound⟩ := actual_normalized_recursion
  refine ⟨K,recursionConstant C D,hK,recursionConstant_pos C D,?_⟩
  filter_upwards [hbound] with x hx
  rcases hx with ⟨hP,hs,hm⟩
  refine ⟨hP,hs,?_⟩
  exact uniform_moment_bound hs hC.le hD.le
    (fun q hq0 hq1 => ⟨(hm q hq0 hq1).1,(hm q hq0 hq1).2.1⟩)
    (fun q hq0 hq1 => (hm q hq0 hq1.le).2.2 hq1)

theorem actual_source_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 →
      (∫ ω, (unitEnergy (sourceCutoff x) 0 ω)^q ∂phaseMeasure) ≤
        C*(Real.log (sourceCutoff x)/momentWeight (Real.sqrt (Real.log (Real.log x))) q)^q := by
  obtain ⟨K,H,hK,hH,hbound⟩ := actual_normalized_moment_bound
  refine ⟨H*max 1 K,mul_pos hH (lt_of_lt_of_le (by norm_num) (le_max_left _ _)),?_⟩
  filter_upwards [hbound] with x hx
  rcases hx with ⟨hP,hs,hm⟩
  intro q hq0 hq1
  have hq : 0 ≤ q := by linarith
  have hl : 0 < Real.log (sourceCutoff x) := Real.log_pos hP
  have hw := momentWeight_ge_one hs.le hq1
  have h := hm q hq0 hq1
  rw [normalizedMoment_eq hP.le hK.le] at h
  have hden := Real.rpow_pos_of_pos (mul_pos hK hl) q
  have hraw := (div_le_iff₀ hden).mp h
  calc
    _ ≤ (H/(momentWeight (Real.sqrt (Real.log (Real.log x))) q)^q)*
        (K*Real.log (sourceCutoff x))^q := hraw
    _ = H*K^q*(Real.log (sourceCutoff x)/momentWeight (Real.sqrt (Real.log (Real.log x))) q)^q := by
      rw [Real.mul_rpow hK.le hl.le,Real.div_rpow hl.le (by linarith)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_le_max_one hK.le hq hq1) hH.le)
      (Real.rpow_nonneg (div_nonneg hl.le (by linarith)) q)

theorem sourceCutoff_power {P : ℝ} (hP : 0 ≤ P) : sourceCutoff (P^(Real.exp 1)) = P := by
  unfold sourceCutoff
  rw [← Real.rpow_mul hP]
  have he : Real.exp 1*(1/Real.exp 1) = 1 := by field_simp
  rw [he,Real.rpow_one]

theorem log_log_source_power {P : ℝ} (hP : 1 < P) :
    Real.log (Real.log (P^(Real.exp 1))) = 1+Real.log (Real.log P) := by
  rw [Real.log_rpow (by linarith : 0 < P),
    Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt (Real.log_pos hP)),Real.log_exp]

theorem critical_low_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
      unitFractionalMoment P ≤
        C*(Real.log P/(1+(1/4)*Real.sqrt (Real.log (Real.log P))))^(3/4 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := actual_source_moment_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_rpow_atTop (Real.exp_pos 1)).eventually hbound,
    eventually_gt_atTop (1 : ℝ)] with P hP hP1
  have h := hP (3/4) le_rfl (by norm_num)
  rw [sourceCutoff_power (by linarith : 0 ≤ P),log_log_source_power hP1] at h
  norm_num only [momentWeight,show 1-(3/4 : ℝ)=1/4 by norm_num] at h
  change unitFractionalMoment P ≤ _ at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (div_nonneg (Real.log_pos hP1).le (by positivity)) _ (by norm_num)
  apply div_le_div_of_nonneg_left (Real.log_pos hP1).le (by positivity)
  have hs := Real.sqrt_le_sqrt (show Real.log (Real.log P) ≤ 1+Real.log (Real.log P) by linarith)
  linarith

end NField.Alignment.HarperCriticalLowMoment
