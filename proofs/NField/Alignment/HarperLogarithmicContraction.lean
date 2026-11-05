/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianMovingSplit

/-!
# Half-time contraction for the logarithmic upper barrier

Over a doubling of time the barrier rises by at most ten. At sufficiently
large half length, this is absorbed by the Gaussian endpoint threshold.
The uniform logarithmic deficit budget supplies the other term.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLogarithmicContraction
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperMovingKilledPath HarperLogarithmicDrift
  HarperGaussianMovingSplit HarperGaussianEndpointLaw

theorem logBoundary_doubling {m : ℕ} (hm : 0 < m) (a : ℝ) :
    logBoundary a (m+m)-logBoundary a m ≤ 10 := by
  rw [logBoundary_positive_time a (by omega : 0 < m+m),logBoundary_positive_time a hm]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : ((m+m : ℕ) : ℝ) = 2*(m : ℝ) := by push_cast; ring
  rw [he,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm0.ne']
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem gaussian_logarithmic_half_recurrence {m : ℕ} (hm : 160000 ≤ m)
    (v : Fin (m+m) → NNReal) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent (logBoundary a)) ≤
      40*logDeficitConstant*(a+1)/Real.sqrt (m : ℝ)+
        (3/5)*(Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd m i)))).real
          (movingEvent (logBoundary a)) := by
  have hmpos : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hlarge : 400 ≤ Real.sqrt (m : ℝ) := by
    have hmr : (160000 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.sq_sqrt hm0.le,Real.sqrt_nonneg (m : ℝ)]
  have hsplit := gaussian_moving_split v
    (by simpa only [logBoundary_zero] using ha : 0 ≤ logBoundary a 0) (Real.sqrt (m : ℝ)/40)
  have htail := gaussian_logarithmic_deficit_tail ha
    (show 0 ≤ Real.sqrt (m : ℝ)/40 by positivity)
    (fun i => v (Fin.castAdd m i)) (fun i => hv _)
  have hdelta := logBoundary_doubling hmpos a
  have hcut : Real.sqrt (m : ℝ)/40+(logBoundary a (m+m)-logBoundary a m) ≤
      Real.sqrt (m : ℝ)/20 := by linarith
  have hend := gaussian_sum_endpoint_contraction hmpos
    (fun i => v (Fin.natAdd m i)) (fun i => (hv _).1)
  have hmono := measureReal_mono
    (μ := Measure.pi (fun i : Fin m => gaussianReal 0 (v (Fin.natAdd m i))))
    (show {z : Fin m → ℝ | (∑ i, z i) ≤ Real.sqrt (m : ℝ)/40+
        (logBoundary a (m+m)-logBoundary a m)} ⊆ {z | (∑ i, z i) ≤ Real.sqrt (m : ℝ)/20}
      from fun _ hz => hz.trans hcut) (by finiteness)
  have hmul := mul_le_mul_of_nonneg_left (hmono.trans hend)
    (show 0 ≤ (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd m i)))).real
      (movingEvent (logBoundary a)) from measureReal_nonneg)
  have hc : 0 ≤ logDeficitConstant*(a+1) := mul_nonneg logDeficitConstant_pos.le (by linarith)
  have hdiv := div_le_div_of_nonneg_left hc
    (show 0 < Real.sqrt (m : ℝ)/40 by positivity)
    (show Real.sqrt (m : ℝ)/40 ≤ Real.sqrt (m : ℝ)/40+2 by linarith)
  have he : logDeficitConstant*(a+1)/(Real.sqrt (m : ℝ)/40) =
      40*logDeficitConstant*(a+1)/Real.sqrt (m : ℝ) := by field_simp
  rw [he] at hdiv
  nlinarith

end NField.Alignment.HarperLogarithmicContraction
