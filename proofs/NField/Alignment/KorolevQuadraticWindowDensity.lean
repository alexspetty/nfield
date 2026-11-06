/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowDensity

/-! # Quadratic size conditions for actual selected-window prime populations -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevQuadraticWindowDensity
open KorolevPrimeWindows KorolevWindowMass KorolevWindowDensity

/-- The exponential endpoint absorbs the divisor loss already at a quadratic index scale. -/
theorem endpoint_ge_of_quadratic_size {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hsize : 36*(k : ℝ)^2 ≤ L) :
    16*(k : ℝ)*(2*(k : ℝ)+1) ≤ lowerEndpoint L k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 ≤ L := (by positivity : 0 ≤ 36*(k : ℝ)^2).trans hsize
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  have hq : 12*(k : ℝ) ≤ L/(2*(k : ℝ)+1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hl := hq.trans (log_lower_ge hL hk)
  have hx : 0 ≤ Real.log (lowerEndpoint L k) := by linarith
  have he := Real.quadratic_le_exp_of_nonneg hx
  rw [Real.exp_log (lowerEndpoint_pos L k)] at he
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 12*(k : ℝ)) hl 2
  nlinarith [sq_nonneg (k : ℝ)]

/-- Actual coprime prime populations under quadratic size conditions, with no cubic restriction. -/
theorem coprime_window_population_ge_quadratic {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hfirst : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hsecond : 36*(k : ℝ)^2 ≤ Real.log m) :
    lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
      (((windowPrimes (Real.log m) k).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  obtain ⟨hL, _, htwo, _⟩ := window_conditions hk hsize
  have hu := lowerEndpoint_pos (Real.log m) k
  have hlog := log_lower_ge hL.le hk
  have hulower := endpoint_ge_of_quadratic_size hk hsecond
  have he1 : lossConstant*(k : ℝ)/Real.log m ≤ 1/(16*(k : ℝ)) := by
    apply (div_le_div_iff₀ hL (by positivity : 0 < 16*(k : ℝ))).mpr
    nlinarith only [hfirst]
  have he2 : Real.log m /
      (lowerEndpoint (Real.log m) k * Real.log (lowerEndpoint (Real.log m) k)) ≤
      1/(16*(k : ℝ)) := by
    have hlo : 0 < Real.log (lowerEndpoint (Real.log m) k) := Real.log_pos (by linarith)
    have hh := (div_le_iff₀ hd).mp hlog
    have hr : Real.log m /
        (lowerEndpoint (Real.log m) k * Real.log (lowerEndpoint (Real.log m) k)) ≤
        (2*(k : ℝ)+1)/lowerEndpoint (Real.log m) k := by
      apply (div_le_div_iff₀ (mul_pos hu hlo) hu).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right hh hu.le
    apply hr.trans
    apply (div_le_div_iff₀ hu (by positivity : 0 < 16*(k : ℝ))).mpr
    nlinarith only [hulower]
  apply coprime_window_population_ge hm hk hsize
  have he : 1/(8*(k : ℝ)) = 1/(16*(k : ℝ)) + 1/(16*(k : ℝ)) := by ring
  rw [he]
  exact add_le_add he1 he2

end NField.Alignment.KorolevQuadraticWindowDensity
