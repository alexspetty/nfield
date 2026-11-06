/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeEulerLog
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Normalization of the Euler-product branch at the right end of the plane -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.EulerLogNormalization

open scoped Topology
open Filter
open NField.Alignment.PrimeEulerLog

theorem eulerLogTerm_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 2 ≤ s.re) (p : Nat.Primes) :
    ‖-Complex.log (1 - primeTerm χ s p)‖ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-s.re) := by
  have hh : ‖-primeTerm χ s p‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_neg]
    have h := primeTerm_norm_le_two χ (by norm_num : (0 : ℝ) ≤ 2) hs p
    norm_num at h
    linarith
  have h := Complex.norm_log_one_add_half_le_self hh
  have hlog : ‖-Complex.log (1 - primeTerm χ s p)‖ ≤ (3 / 2 : ℝ) * ‖primeTerm χ s p‖ := by
    simpa only [norm_neg, sub_eq_add_neg] using h
  exact hlog.trans (mul_le_mul_of_nonneg_left (primeTerm_norm_le χ s p) (by norm_num))

theorem eulerLogTerm_uniform_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 2 ≤ s.re) (p : Nat.Primes) :
    ‖-Complex.log (1 - primeTerm χ s p)‖ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-2 : ℝ) := by
  refine (eulerLogTerm_bound χ hs p).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)

/-- Title: `The Euler-product logarithm tends to zero whenever the real part tends to infinity`. -/
theorem eulerLog_tendsto_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {α : Type*} {l : Filter α} {s : α → ℂ}
    (hs : Tendsto (fun a => (s a).re) l atTop) :
    Tendsto (fun a => eulerLog χ (s a)) l (𝓝 0) := by
  have hbound : Summable (fun p : Nat.Primes => (3 / 2 : ℝ) * (p : ℝ) ^ (-2 : ℝ)) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left _
  have hevent : ∀ᶠ a in l, 2 ≤ (s a).re := hs.eventually (eventually_ge_atTop 2)
  have hterm (p : Nat.Primes) :
      Tendsto (fun a => -Complex.log (1 - primeTerm χ (s a) p)) l (𝓝 0) := by
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
    have hpow : Tendsto (fun a => (p : ℝ) ^ (-(s a).re)) l (𝓝 0) := by
      simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p), Function.comp_def] using
        tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop_of_base_gt_one (p : ℝ) hp).comp hs)
    apply squeeze_zero_norm' (hevent.mono (fun a ha => eulerLogTerm_bound χ ha p))
    simpa using hpow.const_mul (3 / 2 : ℝ)
  have h := tendsto_tsum_of_dominated_convergence hbound hterm
    (hevent.mono (fun a ha p => eulerLogTerm_uniform_bound χ ha p))
  simpa only [eulerLog, primeTerm, tsum_zero] using h

end NField.Alignment.EulerLogNormalization
