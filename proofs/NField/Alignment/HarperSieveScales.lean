/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSieveApplications
import NField.Alignment.HarperSmoothCountDecay

/-!
# Sieve estimates at the actual rounded Harper scales

The constructed interval bound controls both smoothing consumers:
the full error is eventually at most 4*x/log(P), and the short-interval
weight is at most 3/log(P) uniformly for t >= y. Every scale condition is
proved for the manuscript's P, y and X. The three-quarter error is negligible
at targetScale, and the sieve bound is inserted into actual random conditioning.
-/

noncomputable section
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology

namespace NField.Alignment.HarperSieveScales

open HarperRoundedCutoff HarperSmoothingConditioning HarperSieveApplications
  HarperRoughSmoothing HarperActualConditioning HarperConditioningFrequencies
  HarperSmoothCountDecay HarperConditioningDecay

theorem cutoffLog_le_sqrt {x : ℝ} (hx : 1 ≤ x) (hell : 1 ≤ cutoffLog x) :
    cutoffLog x ≤ Real.sqrt (Real.log x) := by
  have hp := cutoffLog_sixth_le hx
  have hpow : (cutoffLog x)^2 ≤ (cutoffLog x)^6 :=
    pow_le_pow_right₀ hell (by norm_num)
  exact (Real.le_sqrt (cutoffLog_nonneg x) (Real.log_nonneg hx)).mpr (hpow.trans hp)

theorem eventual_primePower_mul_cutoff_le (k : ℕ) : ∀ᶠ x : ℝ in atTop,
    (primeCutoff x)^k * cutoffLog x ≤ x := by
  have hb := (cutoffLog_isLittleO_log.const_mul_left ((k : ℝ)+1)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (cutoffLog_nonneg x)),
    Real.norm_of_nonneg (Real.log_pos hx1).le, one_mul] at hx
  calc
    _ ≤ (primeCutoff x)^k * Real.exp (cutoffLog x) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (cutoffLog x)]) (by unfold primeCutoff; positivity)
    _ = Real.exp (((k : ℝ)+1)*cutoffLog x) := by
      rw [primeCutoff, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hx
    _ = x := Real.exp_log hx0

theorem eventual_smoothing_polynomial_bound : ∀ᶠ x : ℝ in atTop,
    (1+Real.log x)*cutoffLog x ≤ smoothingScale x := by
  have hb := (Real.isLittleO_pow_exp_atTop (n := 3)).bound (by norm_num : (0 : ℝ) < 1/2)
  have ht : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually hb, cutoffLog_tendsto.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
    with x hexp hell hlog hx
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hu0 := Real.sqrt_nonneg (Real.log x)
  have hu1 : 1 ≤ Real.sqrt (Real.log x) := (Real.le_sqrt (by norm_num) hlog0).mpr (by nlinarith)
  have hu2 := Real.sq_sqrt hlog0
  have hellu := cutoffLog_le_sqrt hx hell
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hexp
  calc
    _ ≤ (1+Real.log x)*Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_left hellu (by linarith)
    _ ≤ 2*(Real.sqrt (Real.log x))^3 := by nlinarith
    _ ≤ smoothingScale x := by dsimp [smoothingScale]; linarith


theorem eventual_roughSmoothingError_bound : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ,
    roughSmoothingError x (primeCutoff x) y (smoothingScale x) ≤
      4*x/Real.log (primeCutoff x) := by
  have hPt : Tendsto primeCutoff atTop atTop := Real.tendsto_exp_atTop.comp cutoffLog_tendsto
  filter_upwards [eventual_primePower_mul_cutoff_le 4, eventual_smoothing_polynomial_bound,
    hPt.eventually_ge_atTop 2, cutoffLog_tendsto.eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℝ)] with x hpow hpoly hP hell hx
  intro y
  have hX : 0 < smoothingScale x := Real.exp_pos _
  have hlog : 0 < Real.log (primeCutoff x) := by rwa [log_primeCutoff]
  have hp : (primeCutoff x)^4 ≤ x/Real.log (primeCutoff x) := by
    rw [log_primeCutoff]
    exact (le_div_iff₀ hell).mpr hpow
  have hw : x/smoothingScale x*(1+Real.log x) ≤ x/Real.log (primeCutoff x) := by
    have hf : (1+Real.log x)/smoothingScale x ≤ 1/cutoffLog x :=
      (div_le_div_iff₀ hX hell).mpr (by simpa only [one_mul] using hpoly)
    have h := mul_le_mul_of_nonneg_left hf (zero_le_one.trans hx)
    rw [log_primeCutoff]
    calc
      x/smoothingScale x*(1+Real.log x) = x*((1+Real.log x)/smoothingScale x) := by ring
      _ ≤ x*(1/cutoffLog x) := h
      _ = x/cutoffLog x := by ring
  have hb := roughSmoothingError_bound hx hP hX y
  calc
    _ ≤ 2*x/Real.log (primeCutoff x)+(primeCutoff x)^4+
        x/smoothingScale x*(1+Real.log x) := hb
    _ ≤ 2*x/Real.log (primeCutoff x)+x/Real.log (primeCutoff x)+
        x/Real.log (primeCutoff x) := add_le_add (add_le_add le_rfl hp) hw
    _ = _ := by ring

theorem roughSmoothingError_isBigO :
    (fun x => roughSmoothingError x (primeCutoff x) (smoothCutoff x) (smoothingScale x))
      =O[atTop] (fun x => x/Real.log (primeCutoff x)) := by
  apply IsBigO.of_bound 4
  filter_upwards [eventual_roughSmoothingError_bound, eventually_ge_atTop (1 : ℝ),
    cutoffLog_tendsto.eventually_gt_atTop 0] with x hb hx hell
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hlog : 0 < Real.log (primeCutoff x) := by rwa [log_primeCutoff]
  have hnonneg : 0 ≤ roughSmoothingError x (primeCutoff x) (smoothCutoff x) (smoothingScale x) := by
    unfold roughSmoothingError smoothingScale
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (div_nonneg hx0 hlog.le)]
  simpa only [mul_div_assoc] using hb (smoothCutoff x)

theorem prime_square_roughSmoothingError_isBigO :
    (fun p : ℕ => roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
      (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1))) =O[atTop]
      (fun p : ℕ => ((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1))) :=
  roughSmoothingError_isBigO.comp_tendsto base_minus_one_tendsto

theorem eventual_smoothing_sieve_scale : ∀ᶠ x : ℝ in atTop,
    (smoothingScale x+1)*(primeCutoff x)^4*Real.log (primeCutoff x) ≤ smoothCutoff x := by
  have hb := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).bound
    (by norm_num : (0 : ℝ) < 1/7)
  filter_upwards [Real.tendsto_log_atTop.eventually hb,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    cutoffLog_tendsto.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)]
    with x hsmall hll hL hell hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have hu0 := Real.sqrt_nonneg (Real.log x)
  have hu1 : 1 ≤ Real.sqrt (Real.log x) := (Real.le_sqrt (by norm_num) hL0).mpr (by nlinarith)
  have hu2 := Real.sq_sqrt hL0
  have hellu := cutoffLog_le_sqrt hx.le hell
  dsimp only [Function.comp_apply] at hll
  rw [Real.norm_of_nonneg hll.le, Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
    ← Real.sqrt_eq_rpow] at hsmall
  have hfront : 7*Real.sqrt (Real.log x) ≤ Real.log x/Real.log (Real.log x) := by
    apply (le_div_iff₀ hll).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsmall hu0]
  have hX : 2 ≤ smoothingScale x := by
    exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hu1)
  have hellExp : cutoffLog x ≤ smoothingScale x := by
    have h := Real.add_one_le_exp (Real.sqrt (Real.log x))
    dsimp [smoothingScale]
    linarith
  have hP : (primeCutoff x)^4 ≤ Real.exp (4*Real.sqrt (Real.log x)) := by
    rw [primeCutoff, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  calc
    _ ≤ (2*smoothingScale x)*Real.exp (4*Real.sqrt (Real.log x))*smoothingScale x := by
      rw [log_primeCutoff]
      exact mul_le_mul (mul_le_mul (by linarith : smoothingScale x+1 ≤ 2*smoothingScale x)
        hP (by positivity) (by positivity)) hellExp (cutoffLog_nonneg x) (by positivity)
    _ = 2*Real.exp (6*Real.sqrt (Real.log x)) := by
      dsimp [smoothingScale]
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (Real.sqrt (Real.log x))*Real.exp (6*Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le
    _ = Real.exp (7*Real.sqrt (Real.log x)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log x/Real.log (Real.log x)) := Real.exp_le_exp.mpr hfront
    _ = smoothCutoff x := by rw [smoothCutoff, Real.rpow_def_of_pos hx0]; congr 1; ring

theorem eventual_roughShortWeight_bound : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    smoothCutoff x ≤ t → roughShortWeight t (primeCutoff x) (smoothingScale x) ≤
      3/Real.log (primeCutoff x) := by
  have hPt : Tendsto primeCutoff atTop atTop := Real.tendsto_exp_atTop.comp cutoffLog_tendsto
  filter_upwards [eventual_smoothing_sieve_scale, hPt.eventually_ge_atTop 2,
    eventually_gt_atTop (0 : ℝ)] with x hs hP hx
  intro t ht
  have hy : 0 < smoothCutoff x := Real.rpow_pos_of_pos hx _
  exact roughShortWeight_le_three (hy.trans_le ht) hP (Real.exp_pos _) (hs.trans ht)


theorem roughSmoothingError_fractional_isLittleO :
    (fun x => (roughSmoothingError x (primeCutoff x) (smoothCutoff x)
      (smoothingScale x))^(3/4 : ℝ)) =o[atTop] targetScale := by
  have hloglog : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] cutoffLog :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp_tendsto
      Real.tendsto_log_atTop).trans_isBigO cutoffLog_asymptotic.symm.isBigO
  have hg : ∀ᶠ x : ℝ in atTop, 0 ≤ x/Real.log (Real.log x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with x hx hu
    exact div_nonneg hx.le hu.le
  have hb : (fun x => roughSmoothingError x (primeCutoff x) (smoothCutoff x)
      (smoothingScale x)) =O[atTop] (fun x => x/Real.log (Real.log x)) := by
    refine roughSmoothingError_isBigO.trans (IsBigO.of_bound' ?_)
    filter_upwards [hloglog.bound (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (0 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
      cutoffLog_tendsto.eventually_gt_atTop 0] with x hle hx hll hell
    dsimp only [Function.comp_apply] at hll
    rw [Real.norm_of_nonneg hll.le, Real.norm_of_nonneg (cutoffLog_nonneg x), one_mul] at hle
    rw [log_primeCutoff, Real.norm_of_nonneg (div_nonneg hx.le hell.le),
      Real.norm_of_nonneg (div_nonneg hx.le hll.le)]
    exact div_le_div_of_nonneg_left hx.le hll hle
  have hpow := hb.rpow (by norm_num : (0 : ℝ) ≤ 3/4) hg
  have he : (fun x : ℝ => (x/Real.log (Real.log x))^(3/4 : ℝ)) =ᶠ[atTop]
      (fun x => x^(3/4 : ℝ)*(Real.log (Real.log x))^(-(3/4 : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with x hx hu
    dsimp only [Function.comp_apply] at hu
    rw [Real.div_rpow hx.le hu.le, Real.rpow_neg hu.le, div_eq_mul_inv]
  exact (hpow.congr' Filter.EventuallyEq.rfl he).trans_isLittleO
    ((isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO
      (inverse_power_isLittleO.comp_tendsto (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)))

theorem prime_square_roughSmoothingError_fractional_isLittleO :
    (fun p : ℕ => (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
      (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  roughSmoothingError_fractional_isLittleO.comp_tendsto base_minus_one_tendsto

theorem eventual_actual_random_smoothing_sieved : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      (boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
        (smoothRoughAverage ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)) (fun _ => 1)) +
       (4*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_smoothing,
    base_minus_one_tendsto.eventually eventual_roughSmoothingError_bound,
    eventually_ge_atTop (1 : ℕ)] with p hb he hp
  have hx : 0 ≤ (p : ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hp)
  have hnonneg : 0 ≤ roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
      (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)) := by
    unfold roughSmoothingError smoothingScale
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hpow := Real.rpow_le_rpow hnonneg (he (smoothCutoff ((p : ℝ)-1)))
    (by norm_num : (0 : ℝ) ≤ 3/4)
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hpow)
    (Real.rpow_nonneg (by norm_num) _))

end NField.Alignment.HarperSieveScales
