/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicSeed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The actual series in the harmonic-root identity

These are the printed harmonic power, cubic cosine and quadratic sine
series. Absolute majorants give their endpoint continuity independently
of the logarithmic derivative identities still needed on the open arc.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicRootSeries

open scoped BigOperators
open CollisionAmplitudeArithmetic CollisionHarmonicSeed

def harmonicPowerTerm (z : ℂ) (n : ℕ) : ℂ := (harmonicKernel n : ℂ)*z^n

def harmonicPolylog (z : ℂ) : ℂ := ∑' n, harmonicPowerTerm z n

def cubicCosineTerm (θ : ℝ) (n : ℕ) : ℝ := Real.cos ((n : ℝ)*θ)/(n : ℝ)^3

def cubicCosine (θ : ℝ) : ℝ := ∑' n, cubicCosineTerm θ n

def quadraticSineTerm (θ : ℝ) (n : ℕ) : ℝ := Real.sin ((n : ℝ)*θ)/(n : ℝ)^2

def quadraticSine (θ : ℝ) : ℝ := ∑' n, quadraticSineTerm θ n

def harmonicBoundary (θ : ℝ) : ℂ := harmonicPolylog (Complex.exp ((θ : ℂ)*Complex.I))

theorem harmonicPowerTerm_bound {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖harmonicPowerTerm z n‖ ≤ harmonicKernel n := by
  rw [harmonicPowerTerm,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (harmonicKernel_nonneg n),norm_pow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg z) hz) (harmonicKernel_nonneg n)

theorem harmonicPowerTerm_summable {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (harmonicPowerTerm z) :=
  Summable.of_norm_bounded harmonicKernel_hasSum.summable (harmonicPowerTerm_bound hz)

theorem harmonicPolylog_continuousOn : ContinuousOn harmonicPolylog {z : ℂ | ‖z‖ ≤ 1} := by
  unfold harmonicPolylog
  apply continuousOn_tsum (fun n => ?_) harmonicKernel_hasSum.summable
    (fun n z hz => harmonicPowerTerm_bound hz n)
  unfold harmonicPowerTerm
  fun_prop

theorem cubicCosineTerm_bound (θ : ℝ) (n : ℕ) :
    ‖cubicCosineTerm θ n‖ ≤ cubeKernel n := by
  rw [cubicCosineTerm,norm_div,norm_pow,Real.norm_natCast,cubeKernel]
  exact div_le_div_of_nonneg_right
    (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((n : ℝ)*θ)) (by positivity)

theorem quadraticSineTerm_bound (θ : ℝ) (n : ℕ) :
    ‖quadraticSineTerm θ n‖ ≤ 1/(n : ℝ)^2 := by
  rw [quadraticSineTerm,norm_div,norm_pow,Real.norm_natCast]
  exact div_le_div_of_nonneg_right
    (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((n : ℝ)*θ)) (by positivity)

theorem inverseSquare_summable : Summable (fun n : ℕ => 1/(n : ℝ)^2) := by
  simp only [one_div]
  exact Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))

theorem cubicCosineTerm_summable (θ : ℝ) : Summable (cubicCosineTerm θ) :=
  Summable.of_norm_bounded cubeKernel_summable (cubicCosineTerm_bound θ)

theorem quadraticSineTerm_summable (θ : ℝ) : Summable (quadraticSineTerm θ) :=
  Summable.of_norm_bounded inverseSquare_summable (quadraticSineTerm_bound θ)

theorem cubicCosine_continuous : Continuous cubicCosine := by
  unfold cubicCosine
  apply continuous_tsum (fun n => ?_) cubeKernel_summable
    (fun n θ => cubicCosineTerm_bound θ n)
  unfold cubicCosineTerm
  fun_prop

theorem quadraticSine_continuous : Continuous quadraticSine := by
  unfold quadraticSine
  apply continuous_tsum (fun n => ?_) inverseSquare_summable
    (fun n θ => quadraticSineTerm_bound θ n)
  unfold quadraticSineTerm
  fun_prop

theorem circle_exp_norm (θ : ℝ) : ‖Complex.exp ((θ : ℂ)*Complex.I)‖=1 := by
  simp [Complex.norm_exp]

theorem harmonicBoundary_continuous : Continuous harmonicBoundary := by
  unfold harmonicBoundary
  exact harmonicPolylog_continuousOn.comp_continuous (by fun_prop)
    (fun θ => (circle_exp_norm θ).le)

theorem harmonicPolylog_one : harmonicPolylog 1=(zetaThree : ℂ) := by
  rw [harmonicPolylog]
  simp only [harmonicPowerTerm,one_pow,mul_one]
  rw [← Complex.ofReal_tsum,harmonicKernel_hasSum.tsum_eq]

theorem harmonicPolylog_zero : harmonicPolylog 0=0 := by
  unfold harmonicPolylog
  have hzero : ∀ n : ℕ, harmonicPowerTerm 0 n=0 := by
    intro n
    by_cases hn : n=0
    · simp [hn,harmonicPowerTerm,harmonicKernel]
    · simp [harmonicPowerTerm,zero_pow hn]
  simp only [hzero,tsum_zero]

theorem cubicCosine_zero : cubicCosine 0=zetaThree := by
  simp [cubicCosine,cubicCosineTerm,zetaThree,cubeKernel]

theorem quadraticSine_zero : quadraticSine 0=0 := by
  simp [quadraticSine,quadraticSineTerm]

theorem harmonicBoundary_zero : harmonicBoundary 0=(zetaThree : ℂ) := by
  simp [harmonicBoundary,harmonicPolylog_one]

theorem cubicCosineTerm_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t => cubicCosineTerm t n) (-quadraticSineTerm θ n) θ := by
  by_cases hn : n=0
  · simpa [hn,cubicCosineTerm,quadraticSineTerm] using hasDerivAt_const θ (0 : ℝ)
  · convert! (((hasDerivAt_id θ).const_mul (n : ℝ)).cos).div_const ((n : ℝ)^3) using 1
    simp only [quadraticSineTerm,mul_one,id_eq]
    field_simp

theorem cubicCosine_hasDerivAt (θ : ℝ) :
    HasDerivAt cubicCosine (-quadraticSine θ) θ := by
  have h := hasDerivAt_tsum inverseSquare_summable cubicCosineTerm_hasDerivAt
    (fun n t => by simpa only [norm_neg] using quadraticSineTerm_bound t n)
    (cubicCosineTerm_summable 0) θ
  convert! h using 1
  simp only [quadraticSine,tsum_neg]

end NField.Alignment.CollisionHarmonicRootSeries
