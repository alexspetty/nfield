/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralMean
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic kernels for the sharp spectral tail

All integer log-power kernels are summable. The square-log kernel has an
explicit improper integral with its exact leading coefficient.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLogTailKernel

open scoped BigOperators Classical
open Filter MeasureTheory

def logPowerKernel (r : ℕ) (x : ℝ) : ℝ := (Real.log x)^r/x^2
def complexLogPower (r : ℕ) (n : ℕ) : ℂ := (Complex.log n)^r
def kernelTail (x : ℝ) : ℝ := ((Real.log x)^2+2*Real.log x+2)/x

theorem complexLogPower_succ (r : ℕ) :
    complexLogPower (r+1)=LSeries.logMul (complexLogPower r) := by
  funext n
  simp only [complexLogPower,LSeries.logMul,pow_succ]
  ring

theorem complexLogPower_abscissa (r : ℕ) :
    LSeries.abscissaOfAbsConv (complexLogPower r)=1 := by
  induction r with
  | zero =>
      have he : complexLogPower 0=(1 : ℕ → ℂ) := by ext n; simp [complexLogPower]
      rw [he,LSeries.abscissaOfAbsConv_one]
  | succ r ih => rw [complexLogPower_succ,LSeries.abscissaOfAbsConv_logMul,ih]

theorem logPowerKernel_nat_complex (r n : ℕ) :
    (logPowerKernel r n : ℂ)=LSeries.term (complexLogPower r) 2 n := by
  by_cases hn : n=0
  · simp [hn,logPowerKernel,LSeries.term]
  unfold logPowerKernel LSeries.term complexLogPower
  rw [if_neg hn]
  push_cast
  simp only [Complex.cpow_two]

theorem logPowerKernel_nat_summable (r : ℕ) : Summable (fun n : ℕ => logPowerKernel r n) := by
  have hh : LSeries.abscissaOfAbsConv (complexLogPower r)<(2 : ℂ).re := by
    rw [complexLogPower_abscissa]
    change (1 : EReal)<((2 : ℝ) : EReal)
    exact_mod_cast (by norm_num : (1 : ℝ)<2)
  have hs := LSeriesSummable_of_abscissaOfAbsConv_lt_re hh
  change Summable (fun n => LSeries.term (complexLogPower r) 2 n) at hs
  apply Complex.summable_ofReal.mp
  simpa only [logPowerKernel_nat_complex] using hs

theorem squareLogKernel_nonneg (x : ℝ) : 0 ≤ logPowerKernel 2 x := by
  unfold logPowerKernel
  positivity

theorem squareLogKernel_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt (logPowerKernel 2) (2*Real.log x*(1-Real.log x)/x^3) x := by
  have h := ((Real.hasDerivAt_log hx).pow 2).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  convert! h using 1
  dsimp
  field_simp

theorem kernelTail_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt kernelTail (-logPowerKernel 2 x) x := by
  have h := ((((Real.hasDerivAt_log hx).pow 2).add
    ((Real.hasDerivAt_log hx).const_mul 2)).add_const 2).div (hasDerivAt_id x) hx
  convert! h using 1
  dsimp [logPowerKernel]
  field_simp
  ring

theorem negative_kernelTail_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt (fun x => -kernelTail x) (logPowerKernel 2 x) x := by
  have h := (kernelTail_hasDerivAt hx).neg
  simp only [neg_neg] at h
  convert! h using 1

theorem logPower_div_linear_tendsto (r : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x)^r/x) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (r : ℝ)
    (s := 1) (by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast,Real.rpow_one] using h

theorem kernelTail_tendsto_zero : Tendsto kernelTail atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => 2/x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((logPower_div_linear_tendsto 2).add
    ((logPower_div_linear_tendsto 1).const_mul 2)).add h0
  simp only [mul_zero,zero_add] at h
  convert! h using 1
  funext x
  unfold kernelTail
  ring

theorem negative_kernelTail_tendsto_zero :
    Tendsto (fun x => -kernelTail x) atTop (nhds 0) := by
  simpa only [neg_zero] using kernelTail_tendsto_zero.neg

theorem squareLogKernel_integrableOn {Q : ℝ} (hQ : 0 < Q) :
    IntegrableOn (logPowerKernel 2) (Set.Ioi Q) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun _ hx => negative_kernelTail_hasDerivAt (ne_of_gt (hQ.trans_le hx)))
    (fun x _ => squareLogKernel_nonneg x) negative_kernelTail_tendsto_zero

theorem squareLogKernel_integral {Q : ℝ} (hQ : 0 < Q) :
    (∫ x in Set.Ioi Q, logPowerKernel 2 x)=kernelTail Q := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => negative_kernelTail_hasDerivAt (ne_of_gt (hQ.trans_le hx)))
    (fun x _ => squareLogKernel_nonneg x) negative_kernelTail_tendsto_zero
  simpa only [zero_sub,neg_neg] using h

theorem kernelTail_leading_ratio :
    Tendsto (fun x : ℝ => kernelTail x/((Real.log x)^2/x)) atTop (nhds 1) := by
  have hi : Tendsto (fun x : ℝ => 1/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul 2)).add
    ((hi.pow 2).const_mul 2)
  norm_num only [mul_zero,zero_pow,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hl
  have hx0 : x≠0 := by linarith
  have hl0 : Real.log x≠0 := by linarith
  unfold kernelTail
  field_simp

end NField.Alignment.CollisionLogTailKernel
