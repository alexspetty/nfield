/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.Nat

/-!
# The complete-product budget in the Harper comparison

All decimal exponents in the manuscript are exact rational numbers here.
The first estimates use the real variable ell = log P. Rounding and the
integer frequency count are supplied separately, before applying these
bounds to the actual prime-square cutoff.
-/

set_option autoImplicit false

namespace NField.Alignment.HarperParameterBounds

open Filter Asymptotics
open scoped Topology

noncomputable def partitionCount (ell : ℝ) : ℝ := 4 * ell ^ (51/50 : ℝ) + 1

noncomputable def rangeCount (ell : ℝ) : ℕ := ⌈(6/5 : ℝ) * Real.log ell⌉₊

noncomputable def precision (ell : ℝ) : ℝ := ell ^ (-(13/10 : ℝ))

noncomputable def comparisonExponent (ell : ℝ) : ℝ :=
  400 * (partitionCount ell / precision ell)^2 * Real.log ((rangeCount ell : ℝ)*ell)

noncomputable def logCost (ell : ℝ) : ℝ := ell * comparisonExponent ell

theorem partitionCount_pos {ell : ℝ} (hell : 0 ≤ ell) : 0 < partitionCount ell := by
  have h := Real.rpow_nonneg hell (51/50 : ℝ)
  unfold partitionCount
  positivity

theorem precision_pos {ell : ℝ} (h : 0 < ell) : 0 < precision ell :=
  Real.rpow_pos_of_pos h _

theorem partitionCount_le {ell : ℝ} (h : 1 ≤ ell) :
    partitionCount ell ≤ 5 * ell ^ (51/50 : ℝ) := by
  have hpow := Real.one_le_rpow h (by norm_num : (0 : ℝ) ≤ 51/50)
  unfold partitionCount
  linarith

theorem rangeCount_bounds {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    1 ≤ (rangeCount ell : ℝ) ∧
      (6/5 : ℝ)*Real.log ell ≤ (rangeCount ell : ℝ) ∧
      (rangeCount ell : ℝ) ≤ 3*Real.log ell ∧
      (rangeCount ell : ℝ) ≤ 3*ell := by
  have hlo := Nat.le_ceil ((6/5 : ℝ)*Real.log ell)
  have hhi := Nat.ceil_lt_add_one (by positivity : 0 ≤ (6/5 : ℝ)*Real.log ell)
  have hl := Real.log_le_sub_one_of_pos hell
  change (6/5 : ℝ)*Real.log ell ≤ (rangeCount ell : ℝ) at hlo
  change (rangeCount ell : ℝ) < (6/5 : ℝ)*Real.log ell+1 at hhi
  exact ⟨by linarith, hlo, by linarith, by linarith⟩

theorem rangeCount_int_ceil {ell : ℝ} (hlog : 0 ≤ Real.log ell) :
    (rangeCount ell : ℝ) = (⌈(6/5 : ℝ)*Real.log ell⌉ : ℤ) := by
  exact natCast_ceil_eq_intCast_ceil (by positivity)

theorem log_range_product_bound {ell : ℝ} (hell : 0 < ell)
    (hlog : 1 ≤ Real.log ell) :
    0 ≤ Real.log ((rangeCount ell : ℝ)*ell) ∧
      Real.log ((rangeCount ell : ℝ)*ell) ≤ 4*Real.log ell := by
  have hr := rangeCount_bounds hell hlog
  have hell1 : 1 ≤ ell := by
    have h := Real.log_le_sub_one_of_pos hell
    linarith
  have hj : (0 : ℝ) < rangeCount ell := lt_of_lt_of_le zero_lt_one hr.1
  have hprod : (rangeCount ell : ℝ)*ell ≤ 3*ell^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hr.2.2.2 hell.le]
  constructor
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hr.1 hell1)
  · calc
      _ ≤ Real.log (3*ell^2) := Real.log_le_log (mul_pos hj hell) hprod
      _ = Real.log 3 + 2*Real.log ell := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hell.ne'), Real.log_pow]
        norm_num
      _ ≤ 4*Real.log ell := by
        have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith

theorem count_div_precision_bound {ell : ℝ} (hell : 1 ≤ ell) :
    partitionCount ell / precision ell ≤ 5*ell^(58/25 : ℝ) := by
  have hp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  rw [div_eq_mul_inv, precision, Real.rpow_neg hp.le, inv_inv]
  calc
    _ ≤ (5*ell^(51/50 : ℝ))*ell^(13/10 : ℝ) := by
      gcongr
      exact partitionCount_le hell
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hp]
      norm_num

/-- The exact exponent 5.64 is obtained before the asymptotic comparison. -/
theorem logCost_bound {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    0 ≤ logCost ell ∧ logCost ell ≤ 40000*ell^(141/25 : ℝ)*Real.log ell := by
  have hell1 : 1 ≤ ell := by
    have h := Real.log_le_sub_one_of_pos hell
    linarith
  have hr := log_range_product_bound hell hlog
  have hr0 := hr.1
  have hr1 := hr.2
  have hc := count_div_precision_bound hell1
  have hratio : 0 ≤ partitionCount ell / precision ell :=
    (div_pos (partitionCount_pos hell.le) (precision_pos hell)).le
  have hpow : ell * (ell^(58/25 : ℝ))^2 = ell^(141/25 : ℝ) := by
    rw [← Real.rpow_mul_natCast hell.le]
    conv_lhs => lhs; rw [← Real.rpow_one ell]
    rw [← Real.rpow_add hell]
    norm_num
  constructor
  · unfold logCost comparisonExponent
    positivity
  · calc
      logCost ell ≤ ell * (400*(5*ell^(58/25 : ℝ))^2 * (4*Real.log ell)) := by
        unfold logCost comparisonExponent
        gcongr
      _ = 40000*(ell*(ell^(58/25 : ℝ))^2)*Real.log ell := by ring
      _ = _ := by rw [hpow]

theorem logCost_isBigO : logCost =O[atTop]
    (fun ell : ℝ => ell^(141/25 : ℝ)*Real.log ell) := by
  apply IsBigO.of_bound 40000
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with ell hell hlog
  have h := logCost_bound hell hlog
  rw [Real.norm_of_nonneg h.1, Real.norm_of_nonneg (by positivity)]
  simpa only [mul_assoc] using h.2

theorem logCost_isLittleO_sixth_power :
    logCost =o[atTop] (fun ell : ℝ => ell^6) := by
  have h := (isBigO_refl (fun ell : ℝ => ell^(141/25 : ℝ)) atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 9/25))
  have h' : (fun ell : ℝ => ell^(141/25 : ℝ)*Real.log ell) =o[atTop]
      (fun ell : ℝ => ell^6) := h.congr' Filter.EventuallyEq.rfl (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
    rw [← Real.rpow_add hell]
    norm_num)
  exact logCost_isBigO.trans_isLittleO h'

noncomputable def precisionLoad (ell : ℝ) : ℝ :=
  precision ell * (rangeCount ell : ℝ) * ell^(6/5 : ℝ) * Real.sqrt (Real.log ell)

theorem precisionLoad_bound {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    0 ≤ precisionLoad ell ∧ precisionLoad ell ≤
      3 * (ell^(-(1/10 : ℝ)) * (Real.log ell)^(3/2 : ℝ)) := by
  have hr := (rangeCount_bounds hell hlog).2.2.1
  have hd := precision_pos hell
  have hl : 0 < Real.log ell := by linarith
  have ha : precision ell * ell^(6/5 : ℝ) = ell^(-(1/10 : ℝ)) := by
    rw [precision, ← Real.rpow_add hell]
    norm_num
  have hb : Real.log ell * Real.sqrt (Real.log ell) = (Real.log ell)^(3/2 : ℝ) := by
    calc
      _ = (Real.log ell)^((1 : ℝ)) * (Real.log ell)^(1/2 : ℝ) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hl]; norm_num
  constructor
  · unfold precisionLoad
    positivity
  · calc
      precisionLoad ell ≤ precision ell * (3*Real.log ell) * ell^(6/5 : ℝ) *
          Real.sqrt (Real.log ell) := by
        unfold precisionLoad
        gcongr
      _ = 3*(precision ell*ell^(6/5 : ℝ)) *
          (Real.log ell*Real.sqrt (Real.log ell)) := by ring
      _ = _ := by rw [ha, hb]; ring

theorem precision_majorant_tendsto :
    Tendsto (fun ell : ℝ => ell^(-(1/10 : ℝ)) *
      (Real.log ell)^(3/2 : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3/2 : ℝ)
    (by norm_num : (0 : ℝ) < 1/10)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
  rw [Real.rpow_neg hell.le, div_eq_mul_inv, mul_comm]

/-- The strongest printed precision restriction has vanishing left side. -/
theorem precisionLoad_tendsto : Tendsto precisionLoad atTop (𝓝 0) := by
  have h := precision_majorant_tendsto.const_mul 3
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with ell hell hlog
    exact (precisionLoad_bound hell hlog).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with ell hell hlog
    exact (precisionLoad_bound hell hlog).2

theorem eventual_precision_restriction : ∀ᶠ ell : ℝ in atTop,
    precision ell ≤ 1 / ((rangeCount ell : ℝ)*ell^(6/5 : ℝ)*Real.sqrt (Real.log ell)) := by
  filter_upwards [precisionLoad_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with ell hload hell hlog
  have hr : (0 : ℝ) < rangeCount ell := lt_of_lt_of_le zero_lt_one
    (rangeCount_bounds hell hlog).1
  have hl : 0 < Real.log ell := by linarith
  have hden : 0 < (rangeCount ell : ℝ)*ell^(6/5 : ℝ)*Real.sqrt (Real.log ell) := by
    positivity
  apply (le_div_iff₀ hden).mpr
  simpa only [precisionLoad, mul_assoc] using hload.le

end NField.Alignment.HarperParameterBounds
