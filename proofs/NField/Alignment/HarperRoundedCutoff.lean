/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperParameterBounds
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The rounded cutoff and the eventual prime-square size condition

Taking the integer part before the hundredth power implements the paper's
rounding of (log P)^0.01. All counts are genuine natural numbers. The
resulting complete-product size condition is proved, not assumed.
-/

set_option autoImplicit false

namespace NField.Alignment.HarperRoundedCutoff

open Filter Asymptotics
open scoped Topology
open NField.Alignment.HarperParameterBounds

noncomputable def cutoffRoot (x : ℝ) : ℕ := ⌊(Real.log x)^(1/600 : ℝ)⌋₊

noncomputable def cutoffLog (x : ℝ) : ℝ := (cutoffRoot x : ℝ)^100

noncomputable def primeCutoff (x : ℝ) : ℝ := Real.exp (cutoffLog x)

noncomputable def frequencyRadius (x : ℝ) : ℕ := 2 * (cutoffRoot x)^102

noncomputable def factorCount (x : ℝ) : ℕ := 2 * frequencyRadius x + 1

theorem cutoffLog_nonneg (x : ℝ) : 0 ≤ cutoffLog x := by
  unfold cutoffLog
  positivity

theorem log_primeCutoff (x : ℝ) : Real.log (primeCutoff x) = cutoffLog x :=
  Real.log_exp _

/-- The required one-hundredth power is literally an integer. -/
theorem rounding_identity (x : ℝ) :
    (Real.log (primeCutoff x))^(1/100 : ℝ) = (cutoffRoot x : ℝ) := by
  rw [log_primeCutoff, cutoffLog, ← Real.rpow_natCast_mul (Nat.cast_nonneg _) 100]
  norm_num

theorem frequencyRadius_eq (x : ℝ) :
    (frequencyRadius x : ℝ) = 2*(Real.log (primeCutoff x))^(51/50 : ℝ) := by
  rw [log_primeCutoff, cutoffLog, ← Real.rpow_natCast_mul (Nat.cast_nonneg _) 100]
  norm_num [frequencyRadius]

theorem factorCount_eq (x : ℝ) :
    (factorCount x : ℝ) = partitionCount (cutoffLog x) := by
  simp only [factorCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    frequencyRadius_eq, log_primeCutoff, partitionCount]
  ring

theorem integer_frequency_counts (x : ℝ) :
    (frequencyRadius x : ℝ) = 2*(Real.log (primeCutoff x))^(51/50 : ℝ) ∧
    (factorCount x : ℝ) = 2*(frequencyRadius x : ℝ)+1 ∧
    (factorCount x : ℝ) = partitionCount (cutoffLog x) := by
  exact ⟨frequencyRadius_eq x, by simp only [factorCount, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one], factorCount_eq x⟩

theorem comparison_log_identity (x : ℝ) :
    Real.log ((primeCutoff x)^(comparisonExponent (cutoffLog x))) =
      logCost (cutoffLog x) := by
  change Real.log ((Real.exp (cutoffLog x))^(comparisonExponent (cutoffLog x))) =
    cutoffLog x * comparisonExponent (cutoffLog x)
  rw [Real.log_rpow (Real.exp_pos _), Real.log_exp, mul_comm]

theorem cutoffRoot_tendsto : Tendsto cutoffRoot atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/600)).comp Real.tendsto_log_atTop)

theorem cutoffLog_tendsto : Tendsto cutoffLog atTop atTop :=
  (tendsto_pow_atTop (by norm_num : (100 : ℕ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop.comp cutoffRoot_tendsto)

theorem cutoffLog_sixth_le {x : ℝ} (hx : 1 ≤ x) :
    (cutoffLog x)^6 ≤ Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hf := Nat.floor_le (Real.rpow_nonneg hlog (1/600 : ℝ))
  change (cutoffRoot x : ℝ) ≤ (Real.log x)^(1/600 : ℝ) at hf
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffRoot x)) hf 600
  have hid : ((Real.log x)^(1/600 : ℝ))^600 = Real.log x := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hlog (by norm_num : (600 : ℕ) ≠ 0)
  rw [hid] at h
  simpa only [cutoffLog, ← pow_mul] using h

theorem cutoffLog_le_sixth_root {x : ℝ} (hx : 1 ≤ x) :
    cutoffLog x ≤ (Real.log x)^(1/6 : ℝ) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hf := Nat.floor_le (Real.rpow_nonneg hlog (1/600 : ℝ))
  change (cutoffRoot x : ℝ) ≤ (Real.log x)^(1/600 : ℝ) at hf
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffRoot x)) hf 100
  rw [← Real.rpow_mul_natCast hlog] at h
  norm_num at h
  exact h

/-- Both powers in the displayed logarithmic growth chain are retained. -/
theorem eventual_rounded_logCost_bound : ∀ᶠ x : ℝ in atTop,
    0 ≤ logCost (cutoffLog x) ∧ logCost (cutoffLog x) ≤
      40000 * (Real.log x)^(47/50 : ℝ) * Real.log (Real.log x) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hx hell hlog hloglog
  dsimp only [Function.comp_apply] at hlog hloglog
  have hlogx := Real.log_pos hx
  have hbase := logCost_bound hell hlog
  have hroot := cutoffLog_le_sixth_root hx.le
  have hpow : (cutoffLog x)^(141/25 : ℝ) ≤ (Real.log x)^(47/50 : ℝ) := by
    calc
      _ ≤ ((Real.log x)^(1/6 : ℝ))^(141/25 : ℝ) := by
        gcongr
      _ = _ := by rw [← Real.rpow_mul (Real.log_pos hx).le]; norm_num
  have hlogle : Real.log (cutoffLog x) ≤ Real.log (Real.log x) := by
    calc
      _ ≤ Real.log ((Real.log x)^(1/6 : ℝ)) := Real.log_le_log hell hroot
      _ = (1/6 : ℝ)*Real.log (Real.log x) := Real.log_rpow (Real.log_pos hx) _
      _ ≤ _ := by linarith
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  gcongr

theorem rounded_logCost_isBigO :
    (fun x => logCost (cutoffLog x)) =O[atTop]
      (fun x => (Real.log x)^(47/50 : ℝ)*Real.log (Real.log x)) := by
  apply IsBigO.of_bound 40000
  filter_upwards [eventual_rounded_logCost_bound, eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hx hx1 hloglog
  dsimp only [Function.comp_apply] at hloglog
  have hlogx := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hx.1, Real.norm_of_nonneg (by positivity)]
  simpa only [mul_assoc] using hx.2

theorem rounded_growth_isBigO :
    (fun x => (cutoffLog x)^(141/25 : ℝ)*Real.log (cutoffLog x)) =O[atTop]
      (fun x => (Real.log x)^(47/50 : ℝ)*Real.log (Real.log x)) := by
  apply IsBigO.of_bound'
  filter_upwards [eventually_gt_atTop (1 : ℝ), cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hx hell hlog hloglog
  dsimp only [Function.comp_apply] at hlog hloglog
  have hlogx := Real.log_pos hx
  have hroot := cutoffLog_le_sixth_root hx.le
  have hpow : (cutoffLog x)^(141/25 : ℝ) ≤ (Real.log x)^(47/50 : ℝ) := by
    calc
      _ ≤ ((Real.log x)^(1/6 : ℝ))^(141/25 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_mul hlogx.le]; norm_num
  have hlogle : Real.log (cutoffLog x) ≤ Real.log (Real.log x) := by
    calc
      _ ≤ Real.log ((Real.log x)^(1/6 : ℝ)) := Real.log_le_log hell hroot
      _ = (1/6 : ℝ)*Real.log (Real.log x) := Real.log_rpow hlogx _
      _ ≤ _ := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul hpow hlogle (by linarith) (by positivity)

theorem logarithmic_growth_isLittleO :
    (fun x => (Real.log x)^(47/50 : ℝ)*Real.log (Real.log x)) =o[atTop] Real.log := by
  have h := (isBigO_refl (fun t : ℝ => t^(47/50 : ℝ)) atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3/50))
  have h' : (fun t : ℝ => t^(47/50 : ℝ)*Real.log t) =o[atTop] (fun t => t) :=
    h.congr' Filter.EventuallyEq.rfl (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      norm_num)
  exact h'.comp_tendsto Real.tendsto_log_atTop

theorem logarithmic_growth_chain :
    (fun x => logCost (cutoffLog x)) =O[atTop]
      (fun x => (cutoffLog x)^(141/25 : ℝ)*Real.log (cutoffLog x)) ∧
    (fun x => (cutoffLog x)^(141/25 : ℝ)*Real.log (cutoffLog x)) =O[atTop]
      (fun x => (Real.log x)^(47/50 : ℝ)*Real.log (Real.log x)) ∧
    (fun x => (Real.log x)^(47/50 : ℝ)*Real.log (Real.log x)) =o[atTop] Real.log :=
  ⟨logCost_isBigO.comp_tendsto cutoffLog_tendsto,
    rounded_growth_isBigO, logarithmic_growth_isLittleO⟩

/-- The rounding does not weaken the logarithmic budget. -/
theorem rounded_logCost_isLittleO :
    (fun x => logCost (cutoffLog x)) =o[atTop] Real.log := by
  have h := logCost_isLittleO_sixth_power.comp_tendsto cutoffLog_tendsto
  have hb : (fun x => (cutoffLog x)^6) =O[atTop] Real.log := by
    apply IsBigO.of_bound' 
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (cutoffLog x)^6),
      Real.norm_of_nonneg (Real.log_nonneg hx)]
    exact cutoffLog_sixth_le hx
  exact h.trans_isBigO hb

theorem eventual_logCost_lt_log :
    ∀ᶠ x : ℝ in atTop, logCost (cutoffLog x) < Real.log x := by
  have h := rounded_logCost_isLittleO.def (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog := Real.log_pos hx1
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog.le] at hx
  have hle := (le_abs_self (logCost (cutoffLog x))).trans hx
  linarith

/-- A stronger bound than needed: the complete comparison product is below
x squared, hence below (x+1) squared, for all sufficiently large x. -/
theorem eventual_complete_product_size :
    ∀ᶠ x : ℝ in atTop,
      x * (primeCutoff x)^(comparisonExponent (cutoffLog x)) < x^2 := by
  filter_upwards [eventual_logCost_lt_log, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have heq : (primeCutoff x)^(comparisonExponent (cutoffLog x)) =
      Real.exp (logCost (cutoffLog x)) := by
    exact (Real.exp_mul _ _).symm
  rw [heq]
  have hexp := Real.exp_lt_exp.mpr hx
  rw [Real.exp_log (by linarith : 0 < x)] at hexp
  simpa only [pow_two] using mul_lt_mul_of_pos_left hexp (by linarith : 0 < x)

theorem cutoffLog_ratio_limit : Tendsto
    (fun x => cutoffLog x / (Real.log x)^(1/6 : ℝ)) atTop (𝓝 1) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/600)).comp
    Real.tendsto_log_atTop
  have h : Tendsto
      (fun x : ℝ => ((⌊(Real.log x)^(1/600 : ℝ)⌋₊ : ℝ) /
        (Real.log x)^(1/600 : ℝ))^100) atTop (𝓝 1) := by
    simpa only [one_pow, Function.comp_apply] using
      (tendsto_nat_floor_div_atTop.comp ht).pow 100
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [div_pow, ← Real.rpow_mul_natCast (Real.log_pos hx).le]
  norm_num [cutoffLog, cutoffRoot]

/-- The rounded logarithm is asymptotically equivalent to the sixth root
of log x, which is stronger than the printed two-sided comparison. -/
theorem cutoffLog_asymptotic :
    cutoffLog ~[atTop] (fun x => (Real.log x)^(1/6 : ℝ)) :=
  isEquivalent_of_tendsto_one cutoffLog_ratio_limit

theorem cutoffLog_isLittleO_log : cutoffLog =o[atTop] Real.log := by
  have h : (fun ell : ℝ => ell) =o[atTop] (fun ell => ell^6) := by
    simpa only [pow_one] using (isLittleO_pow_pow_atTop_of_lt
      (by norm_num : (1 : ℕ) < 6) : (fun ell : ℝ => ell^1) =o[atTop] (fun ell => ell^6))
  have hb : (fun x => (cutoffLog x)^6) =O[atTop] Real.log := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (cutoffLog x)^6),
      Real.norm_of_nonneg (Real.log_nonneg hx)]
    exact cutoffLog_sixth_le hx
  exact (h.comp_tendsto cutoffLog_tendsto).trans_isBigO hb

/-- Even prime squares lie below the short cutoff eventually. -/
theorem eventual_cutoff_square_lt : ∀ᶠ x : ℝ in atTop, (primeCutoff x)^2 < x := by
  have hb := (cutoffLog_isLittleO_log.const_mul_left (2 : ℝ)).def
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl := Real.log_pos hx1
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hl.le] at hx
  have hh := (le_abs_self (2*cutoffLog x)).trans hx
  have hlt : 2*cutoffLog x < Real.log x := by linarith
  have h := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_log (by linarith : 0 < x)] at h
  simpa only [primeCutoff, ← Real.exp_nat_mul, Nat.cast_ofNat] using h

noncomputable def smoothCutoff (x : ℝ) : ℝ := x^(1/Real.log (Real.log x))

theorem cutoffLog_mul_loglog_isLittleO :
    (fun x => cutoffLog x * Real.log (Real.log x)) =o[atTop] Real.log := by
  have h := cutoffLog_asymptotic.isBigO.mul_isLittleO
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5/6)).comp_tendsto
      Real.tendsto_log_atTop)
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_add (Real.log_pos hx)]
  norm_num

theorem eventual_cutoff_hierarchy : ∀ᶠ x : ℝ in atTop,
    primeCutoff x < smoothCutoff x ∧ smoothCutoff x < x := by
  have hb := cutoffLog_mul_loglog_isLittleO.def (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 1]
    with x hx hx1 hloglog
  dsimp only [Function.comp_apply] at hloglog
  have hxp : 0 < x := by linarith
  have hl := Real.log_pos hx1
  have hll : 0 < Real.log (Real.log x) := by linarith
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hl.le] at hx
  have hh := (le_abs_self (cutoffLog x * Real.log (Real.log x))).trans hx
  have hlt : cutoffLog x * Real.log (Real.log x) < Real.log x := by linarith
  have hdiv := (lt_div_iff₀ hll).mpr hlt
  constructor
  · rw [primeCutoff, smoothCutoff, Real.rpow_def_of_pos hxp]
    apply Real.exp_lt_exp.mpr
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  · have hexp : 1/Real.log (Real.log x) < (1 : ℝ) := (div_lt_one hll).mpr hloglog
    simpa only [smoothCutoff, Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hx1 hexp

theorem base_minus_one_tendsto :
    Tendsto (fun p : ℕ => (p : ℝ)-1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p : ℝ))
    atTop atTop).eventually_ge_atTop (b+1)] with p hp
  linarith

/-- The manuscript's strict modulus condition, for every sufficiently large
natural base and therefore for every sufficiently large odd prime. -/
theorem eventual_prime_square_size :
    ∀ᶠ p : ℕ in atTop,
      ((p : ℝ)-1) * (primeCutoff ((p : ℝ)-1))^
        (comparisonExponent (cutoffLog ((p : ℝ)-1))) < (p : ℝ)^2 := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_complete_product_size,
    eventually_ge_atTop (2 : ℕ)] with p hsize hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact hsize.trans (by nlinarith)

theorem eventual_prime_square_precision : ∀ᶠ p : ℕ in atTop,
    precision (cutoffLog ((p : ℝ)-1)) ≤ 1 /
      ((rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ) *
        (cutoffLog ((p : ℝ)-1))^(6/5 : ℝ) *
          Real.sqrt (Real.log (cutoffLog ((p : ℝ)-1)))) :=
  base_minus_one_tendsto.eventually
    (cutoffLog_tendsto.eventually eventual_precision_restriction)

end NField.Alignment.HarperRoundedCutoff
