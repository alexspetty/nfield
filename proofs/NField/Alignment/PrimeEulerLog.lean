/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # The actual prime Euler logarithm and its higher-power remainder

The logarithm branch is the sum of the logarithms of the Euler factors.
Mathlib supplies the Euler product, logarithm Taylor series and uniform-sum
criterion. The higher-power term has a summable bound on every closed
half-plane strictly to the right of one half.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PrimeEulerLog

open scoped BigOperators Topology
open Complex Filter

def primeTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (p : Nat.Primes) : ℂ :=
  χ p * (p : ℂ) ^ (-s)

def primeSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, primeTerm χ s p

def eulerLog {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - primeTerm χ s p)

def higherFactor {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - primeTerm χ s p) - primeTerm χ s p

def higherPowerSum {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, higherFactor χ s p

theorem primeTerm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (p : Nat.Primes) :
    ‖primeTerm χ s p‖ ≤ (p : ℝ) ^ (-s.re) := by
  rw [primeTerm, norm_mul, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one p)

theorem primeTerm_norm_le_strip {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖primeTerm χ s p‖ ≤ (p : ℝ) ^ (-σ) := by
  exact (primeTerm_norm_le χ s p).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_le) (neg_le_neg hs))

theorem primeTerm_norm_le_two {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖primeTerm χ s p‖ ≤ (2 : ℝ) ^ (-σ) := by
  exact (primeTerm_norm_le_strip χ hs p).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le)
      (neg_nonpos.mpr hσ))

theorem primeTerm_norm_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    ‖primeTerm χ s p‖ < 1 := by
  exact (primeTerm_norm_le_two χ hs.le le_rfl p).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))

theorem higherFactor_taylor {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    HasSum (fun k : ℕ => primeTerm χ s p ^ (k + 2) / (k + 2))
      (higherFactor χ s p) := by
  have h := (hasSum_nat_add_iff' 2).mpr
    (Complex.hasSum_taylorSeries_neg_log (primeTerm_norm_lt_one χ hs p))
  simpa [higherFactor, Finset.sum_range_succ] using h

theorem higherFactor_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    ‖higherFactor χ s p‖ ≤
      ‖primeTerm χ s p‖ ^ 2 * (1 - ‖primeTerm χ s p‖)⁻¹ / 2 := by
  have h := Complex.norm_log_one_add_sub_self_le
    (z := -primeTerm χ s p) (by simpa using primeTerm_norm_lt_one χ hs p)
  have heq : higherFactor χ s p =
      -(Complex.log (1 + -primeTerm χ s p) - -primeTerm χ s p) := by
    unfold higherFactor
    rw [sub_eq_add_neg]
    ring
  rw [heq, norm_neg]
  simpa only [norm_neg] using h

theorem higherFactor_uniform_majorant {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖higherFactor χ s p‖ ≤
      (p : ℝ) ^ (-2 * σ) * ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2) := by
  have hp := primeTerm_norm_le_strip χ hs p
  have htwo := primeTerm_norm_le_two χ hσ.le hs p
  have hρ : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hσ)
  have hinv : (1 - ‖primeTerm χ s p‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (sub_pos.mpr hρ) (sub_le_sub_left htwo 1)
  have hsq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
    congr 1
    norm_num
    ring
  calc
    ‖higherFactor χ s p‖ ≤
        ‖primeTerm χ s p‖ ^ 2 * (1 - ‖primeTerm χ s p‖)⁻¹ / 2 :=
      higherFactor_norm_le χ (hσ.trans_le hs) p
    _ ≤ ((p : ℝ) ^ (-σ)) ^ 2 * (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 := by
      gcongr
      exact inv_nonneg.mpr (sub_nonneg.mpr (htwo.trans hρ.le))
    _ = _ := by rw [hsq]; ring

/-- Title: `Higher prime powers converge absolutely to the right of one half`. -/
theorem higherPower_norm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖higherFactor χ s p‖) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 * s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  exact (hp.mul_right ((1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (higherFactor_uniform_majorant χ (by linarith) le_rfl)

theorem primeTerm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : Summable (primeTerm χ s) := by
  exact ((Nat.Primes.summable_rpow.mpr (by linarith : -s.re < -1)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (primeTerm_norm_le χ s)).of_norm

/-- Title: `The Euler-product logarithm exponentiates to the actual L-function`. -/
theorem exp_eulerLog_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : Complex.exp (eulerLog χ s) = χ.LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_eulerProduct_exp_log hs

/-- Title: `The prime-character sum is the Euler logarithm minus higher powers`. -/
theorem primeSeries_eq_eulerLog_sub_higherPower {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeSeries χ s = eulerLog χ s - higherPowerSum χ s := by
  have hlog := χ.summable_neg_log_one_sub_mul_prime_cpow hs
  have hp := primeTerm_summable χ hs
  have hsum := hlog.tsum_sub hp
  change higherPowerSum χ s = eulerLog χ s - primeSeries χ s at hsum
  linear_combination hsum

theorem primeTerm_differentiable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : Nat.Primes) : Differentiable ℂ (fun s => primeTerm χ s p) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  exact (differentiable_id.neg.const_cpow (Or.inl hp)).const_mul _

theorem higherFactor_differentiableAt {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun z => higherFactor χ z p) s := by
  have hp := (primeTerm_differentiable χ p).differentiableAt (x := s)
  have hslit : 1 - primeTerm χ s p ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (show ‖-primeTerm χ s p‖ < 1 by simpa using primeTerm_norm_lt_one χ hs p)
  exact ((differentiableAt_const (1 : ℂ)).sub hp).clog hslit |>.neg.sub hp

theorem higherPower_differentiableOn_strip {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    DifferentiableOn ℂ (higherPowerSum χ) {s : ℂ | σ < s.re} := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 * σ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  apply Complex.differentiableOn_tsum_of_summable_norm
    (hp.mul_right ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2))
  · intro p s hs
    exact (higherFactor_differentiableAt χ (by change σ < s.re at hs; linarith) p).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact higherFactor_uniform_majorant χ (by linarith) hs.le p

/-- Title: `The higher-prime-power sum is holomorphic to the right of one half`. -/
theorem higherPower_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (higherPowerSum χ) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change (1 / 2 : ℝ) < s.re at hs
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (higherPower_differentiableOn_strip χ hσ).analyticOnNhd hopen s hσs

theorem primeTerm_pow_div {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    primeTerm χ s p ^ k / k = χ p ^ k / ((k : ℂ) * (p : ℂ) ^ ((k : ℂ) * s)) := by
  rw [primeTerm, mul_pow, ← Complex.cpow_nat_mul]
  rw [show (k : ℂ) * -s = -((k : ℂ) * s) by ring, Complex.cpow_neg]
  ring

/-- The inner series is the literal higher-prime-power series in the manuscript. -/
theorem higherFactor_literal_series {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    HasSum (fun k : ℕ => χ p ^ (k + 2) /
      (((k + 2 : ℕ) : ℂ) * (p : ℂ) ^ (((k + 2 : ℕ) : ℂ) * s)))
      (higherFactor χ s p) := by
  apply (higherFactor_taylor χ hs p).congr_fun
  intro k
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (primeTerm_pow_div χ s p (k + 2)).symm

theorem higherPowerSum_literal_series {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    higherPowerSum χ s = ∑' p : Nat.Primes, ∑' k : ℕ,
      χ p ^ (k + 2) / (((k + 2 : ℕ) : ℂ) * (p : ℂ) ^ (((k + 2 : ℕ) : ℂ) * s)) := by
  exact tsum_congr fun p => (higherFactor_literal_series χ hs p).tsum_eq.symm

theorem primeSeries_differentiableOn_strip {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (primeSeries χ) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (Nat.Primes.summable_rpow.mpr (by linarith : -σ < -1))
  · intro p
    exact (primeTerm_differentiable χ p).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact primeTerm_norm_le_strip χ hs.le p

theorem primeSeries_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (primeSeries χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  change (1 : ℝ) < s.re at hs
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs
  exact (primeSeries_differentiableOn_strip χ hσ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hσs

theorem eulerLog_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (eulerLog χ) {s : ℂ | 1 < s.re} := by
  have h := (primeSeries_analyticOnNhd χ).differentiableOn.add
    ((higherPower_analyticOnNhd χ).differentiableOn.mono (by
      intro s hs
      change (1 / 2 : ℝ) < s.re
      change (1 : ℝ) < s.re at hs
      linarith))
  apply (h.congr ?_).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have heq := primeSeries_eq_eulerLog_sub_higherPower χ hs
  change eulerLog χ s = primeSeries χ s + higherPowerSum χ s
  linear_combination -heq

end NField.Alignment.PrimeEulerLog
