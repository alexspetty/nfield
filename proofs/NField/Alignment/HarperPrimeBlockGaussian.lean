/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianInterval
import NField.Alignment.HarperPrimeBlockVariance

/-!
# Quantitative Gaussian interval law for the actual weighted prime blocks

The real pushforward is the law of the literal Euler-product log norm
under the actual critical weighted measure. Its characteristic function
and the actual normal law have exactly the already proved leading factors.
All variance, cutoff, integrability and smoothing hypotheses are discharged
for sufficiently large upper endpoints, uniformly in index and frequency.
The result is an absolute interval error O(X^(-1/60)), not yet the source's
relative interval estimate or probability barrier.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockGaussian
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set SteinhausMoment HarperEulerIntegral
  HarperTiltedMeasure HarperPrimeBlocks HarperPrimeBlockLaw HarperPrimeRangeCharacteristic
  HarperGaussianSmoothingScales HarperWeightedCharacteristic HarperCharacteristicTaylor
  HarperGaussianInterval HarperPrimeBlockVariance

def blockLaw (x : ℝ) (l : ℕ) (t : ℝ) : Measure ℝ :=
  (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).map (blockLog x l t)
def blockNormalVariance (x : ℝ) (l : ℕ) : ℝ≥0 :=
  ⟨rangeVariance (primeBlock x l), by
    unfold rangeVariance
    exact Finset.sum_nonneg (fun q _ => by positivity)⟩
def blockNormal (x : ℝ) (l : ℕ) (t : ℝ) : Measure ℝ :=
  gaussianReal (rangeMean (primeBlock x l) (fun _ => t)) (blockNormalVariance x l)

theorem blockLaw_probability (x : ℝ) (l : ℕ) (t : ℝ) : IsProbabilityMeasure (blockLaw x l t) := by
  letI := tiltedMeasure_probability (sourceCutoff x)
    (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  exact Measure.isProbabilityMeasure_map (blockLog_measurable x l t).aemeasurable

theorem blockLaw_interval (x : ℝ) (l : ℕ) (t a b : ℝ) :
    (blockLaw x l t).real (Icc a b) =
      (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
        {ω | blockLog x l t ω ∈ Icc a b} := by
  rw [measureReal_def, blockLaw,
    Measure.map_apply (blockLog_measurable x l t) measurableSet_Icc]
  rfl

theorem blockLaw_charFun (x : ℝ) (l : ℕ) (t u : ℝ) :
    charFun (blockLaw x l t) u = blockCharacteristic x l t u := by
  rw [charFun_apply_real, blockLaw, integral_map
    (blockLog_measurable x l t).aemeasurable (by fun_prop)]
  simp only [blockCharacteristic, phaseExponential, Complex.ofReal_mul]

theorem blockNormal_charFun (x : ℝ) (l : ℕ) (t u : ℝ) :
    charFun (blockNormal x l t) u = rangeGaussian (primeBlock x l) (fun _ => t) u := by
  rw [blockNormal, charFun_gaussianReal]
  change Complex.exp ((u : ℂ)*(rangeMean (primeBlock x l) (fun _ => t) : ℂ)*Complex.I-
    (rangeVariance (primeBlock x l) : ℂ)*(u : ℂ)^2/2) = _
  unfold rangeGaussian
  congr 1
  push_cast
  ring

theorem blockLaw_uniform_characteristic_error {x : ℝ} (hx : 1 < x) (l : ℕ)
    (hY : 2 ≤ blockLower x l) (t : ℝ) {u : ℝ}
    (hu : |u| ≤ frequencyCutoff (blockUpper x l)) :
    ‖charFun (blockLaw x l t) u-charFun (blockNormal x l t) u‖ ≤
      4*comparisonConstant*(frequencyCutoff (blockUpper x l)+(frequencyCutoff (blockUpper x l))^3)*
        ((blockUpper x l)^(1/Real.exp 1))^(-(1/2 : ℝ)) := by
  rw [blockLaw_charFun, blockNormal_charFun]
  have hu' : |u| ≤ Real.sqrt (blockLower x l) := by
    rw [blockLower_power (by linarith : 0 ≤ x)]
    exact hu.trans (frequencyCutoff_le_sqrt_lower (blockUpper_gt_one hx l).le)
  apply (blockCharacteristic_gaussian_error hx.le l hY t hu').trans
  rw [blockLower_power (by linarith : 0 ≤ x)]
  have hcube := pow_le_pow_left₀ (abs_nonneg u) hu 3
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
    (Real.rpow_nonneg (by linarith [blockUpper_gt_one hx l] : 0 ≤ blockUpper x l) _) _)
  exact mul_le_mul_of_nonneg_left (add_le_add hu hcube)
    (mul_nonneg (by norm_num) comparisonConstant_pos.le)

theorem blockLaw_interval_error {x : ℝ} (hx : 1 < x) (l : ℕ)
    (hY : 2 ≤ blockLower x l) (hv : (1/4 : ℝ) ≤ blockVariance (blockUpper x l))
    (hd : smoothingWidth (blockUpper x l) ≤ 1) (t a b : ℝ) (hab : b-a ≤ 1) :
    |(blockLaw x l t).real (Icc a b)-(blockNormal x l t).real (Icc a b)| ≤
      intervalComparisonConstant*(blockUpper x l)^(-(1/60 : ℝ)) := by
  letI := blockLaw_probability x l t
  have hv' : (1/4 : ℝ) ≤ rangeVariance (primeBlock x l) := by
    rwa [source_blockVariance (by linarith : 0 ≤ x)]
  exact gaussian_interval_rate (blockLaw x l t) _ (v := blockNormalVariance x l)
    hv' (blockUpper_gt_one hx l).le hd
    (fun u hu => blockLaw_uniform_characteristic_error hx l hY t hu) a b hab

theorem eventual_block_interval_error :
    ∃ X₀ : ℝ, ∀ (x : ℝ), 1 < x → ∀ (l : ℕ), X₀ ≤ blockUpper x l →
      ∀ t a b : ℝ, b-a ≤ 1 →
        |(blockLaw x l t).real (Icc a b)-(blockNormal x l t).real (Icc a b)| ≤
          intervalComparisonConstant*(blockUpper x l)^(-(1/60 : ℝ)) := by
  have he : ∀ᶠ X : ℝ in atTop,
      2 ≤ sourceCutoff X ∧ (1/4 : ℝ) ≤ blockVariance X ∧ smoothingWidth X ≤ 1 := by
    filter_upwards [eventual_cutoff_conditions, eventual_blockVariance_bounds] with X hc hv
    exact ⟨hc.1,hv.1,hc.2.2.2.1⟩
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp he
  refine ⟨X₀,fun x hx l hl t a b hab => ?_⟩
  have h := hX₀ (blockUpper x l) hl
  apply blockLaw_interval_error hx l _ h.2.1 h.2.2 t a b hab
  rw [blockLower_power (by linarith : 0 ≤ x)]
  exact h.1

theorem actual_weighted_interval_error :
    ∃ X₀ : ℝ, ∀ (x : ℝ), 1 < x → ∀ (l : ℕ), X₀ ≤ blockUpper x l →
      ∀ t a b : ℝ, b-a ≤ 1 →
        |(tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
            {ω | blockLog x l t ω ∈ Icc a b}-(blockNormal x l t).real (Icc a b)| ≤
          intervalComparisonConstant*(blockUpper x l)^(-(1/60 : ℝ)) := by
  simpa only [blockLaw_interval] using eventual_block_interval_error

end NField.Alignment.HarperPrimeBlockGaussian
