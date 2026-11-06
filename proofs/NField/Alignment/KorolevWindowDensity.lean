/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowPopulation

/-! # A quantitative positive population criterion for each prime window -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevWindowDensity
open KorolevPrimeWindows KorolevWindowMass KorolevWindowPopulation

/-- The half logarithmic increment has a uniform elementary lower bound. -/
theorem half_log_increment_ge {k : ℕ} (hk : 1 ≤ k) :
    1 / (4*(k : ℝ)) ≤ (Real.log ((k : ℝ)+1)-Real.log k)/2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos (by linarith : (0 : ℝ) < k+1) hk0)
  rw [Real.log_div (by linarith : (k : ℝ)+1 ≠ 0) hk0.ne'] at h
  have hi : 1 - (((k : ℝ)+1)/(k : ℝ))⁻¹ = 1/((k : ℝ)+1) := by
    field_simp
    ring
  rw [hi] at h
  have hd : 1/(2*(k : ℝ)) ≤ 1/((k : ℝ)+1) := by
    apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < k+1)
    linarith
  have he : 1/(4*(k : ℝ)) = (1/(2*(k : ℝ)))/2 := by ring
  rw [he]
  linarith

/-- An explicit endpoint-error inequality gives a lower bound on the actual prime count. -/
theorem coprime_window_population_ge {m k : ℕ} (hm : 0 < m) {L : ℝ} (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ L)
    (hloss : lossConstant*(k : ℝ)/L +
      Real.log m / (lowerEndpoint L k * Real.log (lowerEndpoint L k)) ≤ 1/(8*(k : ℝ))) :
    lowerEndpoint L k / (8*(k : ℝ)) ≤
      (((windowPrimes L k).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hpop := coprime_window_population_lower hm hk hsize
  have hlog := half_log_increment_ge hk
  have hdiff : 1/(8*(k : ℝ)) ≤
      (Real.log ((k : ℝ)+1)-Real.log k)/2 - lossConstant*(k : ℝ)/L -
        Real.log m / (lowerEndpoint L k * Real.log (lowerEndpoint L k)) := by
    have he : 1/(4*(k : ℝ)) = 2*(1/(8*(k : ℝ))) := by ring
    rw [he] at hlog
    linarith
  have h := mul_le_mul_of_nonneg_left hdiff (lowerEndpoint_pos L k).le
  apply le_trans ?_ hpop
  simpa only [mul_one_div] using h

/-- Explicit polynomial size conditions discharge the endpoint and divisor losses. -/
theorem coprime_window_population_ge_of_size {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hfirst : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hsecond : 16*(k : ℝ)*(2*(k : ℝ)+1)^2 ≤ Real.log m) :
    lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
      (((windowPrimes (Real.log m) k).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  obtain ⟨hL, _, htwo, _⟩ := window_conditions hk hsize
  have hu := lowerEndpoint_pos (Real.log m) k
  have hlog := log_lower_ge hL.le hk
  have hquot : 16*(k : ℝ)*(2*(k : ℝ)+1) ≤ Real.log m / (2*(k : ℝ)+1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hexp : Real.log m / (2*(k : ℝ)+1) ≤ lowerEndpoint (Real.log m) k := by
    have he := Real.add_one_le_exp (Real.log (lowerEndpoint (Real.log m) k))
    rw [Real.exp_log hu] at he
    linarith
  have hulower := hquot.trans hexp
  have he1 : lossConstant*(k : ℝ)/Real.log m ≤ 1/(16*(k : ℝ)) := by
    apply (div_le_div_iff₀ hL (by positivity : 0 < 16*(k : ℝ))).mpr
    nlinarith
  have he2 : Real.log m /
      (lowerEndpoint (Real.log m) k * Real.log (lowerEndpoint (Real.log m) k)) ≤
      1/(16*(k : ℝ)) := by
    have hlo : 0 < Real.log (lowerEndpoint (Real.log m) k) := Real.log_pos (by linarith)
    have hh : Real.log m ≤ (2*(k : ℝ)+1)*Real.log (lowerEndpoint (Real.log m) k) :=
      by simpa only [mul_comm] using (div_le_iff₀ hd).mp hlog
    have hr : Real.log m /
        (lowerEndpoint (Real.log m) k * Real.log (lowerEndpoint (Real.log m) k)) ≤
        (2*(k : ℝ)+1)/lowerEndpoint (Real.log m) k := by
      apply (div_le_div_iff₀ (mul_pos hu hlo) hu).mpr
      nlinarith
    apply hr.trans
    apply (div_le_div_iff₀ hu (by positivity : 0 < 16*(k : ℝ))).mpr
    nlinarith
  apply coprime_window_population_ge hm hk hsize
  have he : 1/(8*(k : ℝ)) = 1/(16*(k : ℝ)) + 1/(16*(k : ℝ)) := by ring
  rw [he]
  exact add_le_add he1 he2

end NField.Alignment.KorolevWindowDensity
