/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFactorialDecay
import NField.Alignment.HarperTaylorGrowth
import NField.Alignment.HarperConditioningDecay

/-!
# Decay of the actual complete Taylor-error sum

The factorial gain gives a geometric base at most 2/3. Summing all subset
sizes costs at most 2^A. At the manuscript's rounded parameters this still
decays faster than the required per-box error, including the extra factor
log P needed by the weighted short-sum energy estimate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRemainderDecay

open Filter Asymptotics HarperParameterBounds HarperRoundedCutoff HarperTaylorBudget
  HarperTaylorGrowth HarperPrimeProductMoment HarperPrimeEnergyBound
  HarperProductApproximation HarperFactorialDecay HarperConditioningDecay

def roundedError (x B : ℝ) : ℝ :=
  errorSum (precision (cutoffLog x)) (rangeCount (cutoffLog x))
    (taylorOrder x) (factorCount x) B

theorem eventual_geometric_bound : ∀ᶠ x : ℝ in atTop,
    roundedError x (2 * unitPrimeEnergy (primeCutoff x)) ≤
      6 * (taylorOrder x : ℝ) * factorCount x * 2 ^ factorCount x *
        (2/3 : ℝ) ^ taylorOrder x := by
  filter_upwards [eventual_taylorOrder_bounds, eventual_taylor_data,
    eventual_unitPrimeEnergy_bound (by norm_num : (0 : ℝ) < 1/10),
    cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1]
    with x hg ht henergy hell hlog
  dsimp only [Function.comp_apply] at hlog
  have hd := precision_pos hell
  have hU := unitPrimeEnergy_nonneg (primeCutoff x)
  have hS : (0 : ℝ) < taylorOrder x := by exact_mod_cast ht.2.2.1
  have hj := (rangeCount_bounds hell hlog).1
  have hl : Real.log (cutoffLog x) ≤
      Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) :=
    Real.log_le_log hell (by nlinarith)
  have hL : 0 ≤ Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) := by linarith
  have hB : 2 * unitPrimeEnergy (primeCutoff x) ≤
      (11/5 : ℝ) * Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) := by linarith
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hep : Real.exp 1 * Real.pi ^ 2 ≤ 30 := by
    nlinarith [mul_le_mul Real.exp_one_lt_three.le hpi (sq_nonneg Real.pi)
      (by norm_num : (0 : ℝ) ≤ 3)]
  apply errorSum_geometric hd (by positivity [unitPrimeEnergy_nonneg (primeCutoff x)])
    (by norm_num) (by norm_num) ht.2.2.1 hg.2.2.2
  apply (div_le_iff₀ (by positivity)).mpr
  have hnum : Real.exp 1 * Real.pi ^ 2 * (factorCount x : ℝ) *
      (2 * unitPrimeEnergy (primeCutoff x)) ≤
      66 * (factorCount x : ℝ) * Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) := by
    calc
      _ ≤ 30 * (factorCount x : ℝ) *
          ((11/5 : ℝ) * Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x)) := by
        gcongr
      _ = _ := by ring
  nlinarith [hg.2.2.1]

theorem geometric_power_le_exp (S : ℕ) :
    (2/3 : ℝ) ^ S ≤ Real.exp (-(S : ℝ) / 3) := by
  have hbase : (2/3 : ℝ) ≤ Real.exp (-(1/3 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/3 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1/3 : ℝ))) ^ S := pow_le_pow_left₀ (by norm_num) hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem eventual_polynomial_bound : ∀ᶠ y : ℝ in atTop,
    6 * y ^ 3 ≤ Real.exp (y / 100) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 1/100)).bound
    (by norm_num : (0 : ℝ) < 1/6)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hy
  convert (show 6 * y ^ 3 ≤ Real.exp ((1/100 : ℝ) * y) by linarith) using 1
  congr 1
  ring

theorem geometric_bound_decay {ell : ℝ} {S A : ℕ}
    (hellS : ell ≤ S) (hAS : 100 * (A : ℝ) ≤ S)
    (hpoly : 6 * (S : ℝ) ^ 3 ≤ Real.exp ((S : ℝ) / 100)) :
    ell * (6 * (S : ℝ) * A * 2 ^ A * (2/3 : ℝ) ^ S) ≤
      Real.exp (-(S : ℝ) / 4) := by
  have hA : (A : ℝ) ≤ S := by nlinarith
  have htwo : (2 : ℝ) ^ A ≤ Real.exp ((S : ℝ) / 100) := by
    calc
      _ ≤ (Real.exp 1) ^ A := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _ = Real.exp (A : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hpref : 6 * ell * (S : ℝ) * A ≤ 6 * (S : ℝ) ^ 3 := by
    calc
      _ ≤ 6 * (S : ℝ) * S * S := by gcongr
      _ = _ := by ring
  calc
    _ = (6 * ell * (S : ℝ) * A) * 2 ^ A * (2/3 : ℝ) ^ S := by ring
    _ ≤ Real.exp ((S : ℝ) / 100) * Real.exp ((S : ℝ) / 100) *
        Real.exp (-(S : ℝ) / 3) := by
      gcongr
      · exact hpref.trans hpoly
      · exact geometric_power_le_exp S
    _ = Real.exp ((S : ℝ) / 100 + (S : ℝ) / 100 - (S : ℝ) / 3) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg S (α := ℝ)])

theorem boxError_exp {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    boxError ell = Real.exp (-partitionCount ell * taylorArgument ell) := by
  have hj : (0 : ℝ) < rangeCount ell := lt_of_lt_of_le zero_lt_one (rangeCount_bounds hell hlog).1
  rw [boxError, Real.rpow_def_of_pos (mul_pos hj hell), taylorArgument]
  congr 1
  ring

/-- The full weighted error, including the short-energy logarithm, is at
most the actual eta parameter for all sufficiently large real cutoffs. -/
theorem eventual_weighted_error_le : ∀ᶠ x : ℝ in atTop,
    cutoffLog x * roundedError x (2 * unitPrimeEnergy (primeCutoff x)) ≤ boxError (cutoffLog x) := by
  filter_upwards [eventual_geometric_bound, eventual_taylorOrder_bounds,
    taylorOrder_tendsto.eventually eventual_polynomial_bound,
    cutoffLog_tendsto.eventually_ge_atTop 100,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1]
    with x hg ht hpoly hell hlog
  have hellp : 0 < cutoffLog x := by linarith
  have harg := hell.trans (taylorArgument_ge_self (by linarith : 1 ≤ cutoffLog x) hlog)
  have hlow := taylorOrder_lower harg
  have hR : 0 ≤ (factorCount x : ℝ) * taylorArgument (cutoffLog x) := by positivity
  calc
    _ ≤ cutoffLog x * (6 * (taylorOrder x : ℝ) * factorCount x * 2 ^ factorCount x *
        (2/3 : ℝ) ^ taylorOrder x) := mul_le_mul_of_nonneg_left hg hellp.le
    _ ≤ Real.exp (-(taylorOrder x : ℝ) / 4) :=
      geometric_bound_decay ht.2.1 ht.1 hpoly
    _ ≤ boxError (cutoffLog x) := by
      rw [boxError_exp hellp hlog, ← factorCount_eq]
      apply Real.exp_le_exp.mpr
      nlinarith

theorem eventual_unweighted_error_le : ∀ᶠ x : ℝ in atTop,
    roundedError x (unitPrimeEnergy (primeCutoff x)) ≤ boxError (cutoffLog x) := by
  filter_upwards [eventual_weighted_error_le, cutoffLog_tendsto.eventually_ge_atTop 1] with x hx hell
  have hd := precision_pos (lt_of_lt_of_le zero_lt_one hell)
  have hU := unitPrimeEnergy_nonneg (primeCutoff x)
  calc
    _ ≤ roundedError x (2 * unitPrimeEnergy (primeCutoff x)) :=
      errorSum_mono hd hU (by linarith) _ _ _
    _ ≤ cutoffLog x * roundedError x (2 * unitPrimeEnergy (primeCutoff x)) :=
      le_mul_of_one_le_left (errorSum_nonneg hd (by positivity) _ _ _) hell
    _ ≤ _ := hx

end NField.Alignment.HarperRemainderDecay
