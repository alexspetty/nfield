/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLimitingPrimeProduct
import NField.Alignment.CollisionLimitingPrimeLogSum

/-!
# Explicit logarithmic envelopes with the sharp leading coefficient

The exponential multiplier from large prime divisors tends to one.
Fixed shifts in the logarithmic sum and fixed additive errors disappear
at log-square scale. Composition with log(n) gives the global scale.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLogLogEnvelopes

open Filter Asymptotics CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum

def primeEulerEnvelope (b E x : ℝ) : ℝ :=
  limitingPrimeProduct x*Real.exp (1/Real.log x)*(limitingPrimeLogSum x+b)+E

theorem log_nat_tendsto_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem loglog_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto_atTop

theorem large_prime_multiplier_tendsto :
    Tendsto (fun x : ℝ => Real.exp (1/Real.log x)) atTop (nhds 1) := by
  have h : Tendsto (fun x : ℝ => 1/Real.log x) atTop (nhds 0) := by
    simpa only [Function.comp_def,one_div] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  simpa only [Function.comp_def,Real.exp_zero] using
    (Real.continuous_exp.tendsto 0).comp h

theorem primeEulerEnvelope_asymptotic (b E : ℝ) :
    primeEulerEnvelope b E ~[atTop] (fun x : ℝ => alignmentKappa*(Real.log x)^2) := by
  have hm : (fun x : ℝ => Real.exp (1/Real.log x)) ~[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isEquivalent_const_iff_tendsto (by norm_num : (1 : ℝ) ≠ 0)).mpr
      large_prime_multiplier_tendsto
  have hP : (fun x : ℝ => limitingPrimeProduct x*Real.exp (1/Real.log x)) ~[atTop]
      (fun x : ℝ => alignmentKappa*Real.log x) := by
    have h := limitingPrimeProduct_asymptotic.mul hm
    convert! h using 1
    funext x
    dsimp only [Pi.mul_apply]
    ring
  have hS : (fun x : ℝ => limitingPrimeLogSum x+b) ~[atTop] (fun x : ℝ => Real.log x) :=
    limitingPrimeLogSum_asymptotic.add_isLittleO (constant_isLittleO_log b)
  have hmain : (fun x : ℝ => limitingPrimeProduct x*Real.exp (1/Real.log x)*
      (limitingPrimeLogSum x+b)) ~[atTop] (fun x : ℝ => alignmentKappa*(Real.log x)^2) := by
    have h := hP.mul hS
    convert! h using 1
    funext x
    dsimp only [Pi.mul_apply]
    ring
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun x : ℝ => (Real.log x)^2) := by
    simpa using (constant_isLittleO_log 1).pow (by norm_num : 0 < (2 : ℕ))
  have hE : (fun _ : ℝ => E) =o[atTop] (fun x : ℝ => alignmentKappa*(Real.log x)^2) := by
    simpa only [mul_one] using (h1.const_mul_left E).const_mul_right alignmentKappa_pos.ne'
  exact hmain.add_isLittleO hE

theorem primeEulerEnvelope_log_nat_asymptotic (b E : ℝ) :
    (fun n : ℕ => primeEulerEnvelope b E (Real.log n)) ~[atTop]
      (fun n : ℕ => alignmentKappa*(Real.log (Real.log n))^2) :=
  (primeEulerEnvelope_asymptotic b E).comp_tendsto log_nat_tendsto_atTop

end NField.Alignment.CollisionLogLogEnvelopes
