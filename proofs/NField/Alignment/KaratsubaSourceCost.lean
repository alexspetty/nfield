/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceExponential

/-! # Explicit factorial and index costs in the source bilinear estimate -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourceCost
open KaratsubaSourceExponential KorolevSourceEnvelope Filter
open scoped Topology

/-- The factorial/index numerator is bounded by one explicit prime-index power. -/
theorem factorial_cost_le_power {k s : ℕ} (hs : 1 ≤ s) (hks : k ≤ s) :
    s.factorial*s*(8*k)^k*(8*s)^s*k.factorial ≤ (8*s)^(5*s) := by
  have hs8 : s ≤ 8*s := by omega
  have hk8 : k ≤ 8*s := hks.trans hs8
  have h8 : 8*k ≤ 8*s := Nat.mul_le_mul_left 8 hks
  have hfS := (Nat.factorial_le_pow s).trans
    (pow_le_pow_left₀ (Nat.zero_le s) hs8 s)
  have hfK := (Nat.factorial_le_pow k).trans
    (pow_le_pow_left₀ (Nat.zero_le k) hk8 k)
  have hpK := pow_le_pow_left₀ (Nat.zero_le (8*k)) h8 k
  calc
    _ ≤ (8*s)^s*(8*s)*(8*s)^k*(8*s)^s*(8*s)^k :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hfS hs8) hpK)
        (le_refl ((8*s)^s))) hfK
    _ = (8*s)^s*(8*s)^1*(8*s)^k*(8*s)^s*(8*s)^k := by rw [pow_one]
    _ = (8*s)^(2*s+2*k+1) := by
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ (by omega : 1 ≤ 8*s) (by omega : 2*s+2*k+1 ≤ 5*s)

/-- The full retained cost is at most exp(5*s*log(8*s)). -/
theorem cost_le_exp {k s : ℕ} (hs : 1 ≤ s) (hks : k ≤ s) :
    cost k s ≤ Real.exp (5*(s : ℝ)*Real.log (8*(s : ℝ))) := by
  let n := s.factorial*s*(8*k)^k*(8*s)^s*k.factorial
  have hn : (n : ℝ) ≤ (8*(s : ℝ))^(5*s) := by exact_mod_cast factorial_cost_le_power hs hks
  have hc : cost k s = (n : ℝ)/4 := by
    simp only [cost, n, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hd : (n : ℝ)/4 ≤ n := div_le_self (Nat.cast_nonneg n) (by norm_num)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have he : Real.exp (5*(s : ℝ)*Real.log (8*(s : ℝ))) = (8*(s : ℝ))^(5*s) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.exp_log (by positivity : 0 < 8*(s : ℝ))]
      using Real.exp_nat_mul (Real.log (8*(s : ℝ))) (5*s)
  rw [hc, he]
  exact hd.trans hn

/-- The logarithm of the full index envelope has this exact elementary form. -/
theorem log_eight_envelope (v : ℝ) :
    Real.log (8*envelope v) = Real.log 32+5*v/12 := by
  rw [show 8*envelope v = 32*Real.exp (5*v/12) by unfold envelope; ring]
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]

/-- The squared envelope still has negligible size after the factorial/index logarithmic loss. -/
theorem envelope_log_ratio_tendsto :
    Tendsto (fun v : ℝ => 30*(envelope v)^2*Real.log (8*envelope v)/Real.exp v)
      atTop (𝓝 0) := by
  have hid (v : ℝ) : 30*(envelope v)^2*Real.log (8*envelope v)/Real.exp v =
      480*(Real.log 32+5*v/12)*Real.exp (-v/6) := by
    calc
      _ = 30*Real.log (8*envelope v)*((envelope v)^2/Real.exp v) := by ring
      _ = _ := by rw [envelope_square_ratio, log_eight_envelope]; ring
  have hl : Tendsto (fun v : ℝ => v*Real.exp (-v/6)) atTop (𝓝 0) := by
    simpa [Real.rpow_one, div_eq_mul_inv, neg_mul, mul_comm] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/6) (by norm_num)
  have hc : Tendsto (fun v : ℝ => Real.exp (-v/6)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1/6))
    simpa [Function.comp_def, div_eq_mul_inv, neg_mul, mul_comm] using h
  have ht := (hc.const_mul (480*Real.log 32)).add (hl.const_mul (480*5/12))
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun v => by dsimp only; rw [hid]; ring)

/-- All source-envelope indices absorb the full factorial cost into half the exponent margin. -/
theorem eventual_cost_absorbed : ∀ᶠ v : ℝ in atTop,
    ∀ k s : ℕ, 1 ≤ k → 1 ≤ s → 8*(k : ℝ)^2 ≤ s → (s : ℝ) ≤ envelope v →
      cost k s ≤ Real.exp (Real.exp v/(48*(k : ℝ)^2)) := by
  filter_upwards [envelope_log_ratio_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with v hv k s hk hs hsep hsenv
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hksR : (k : ℝ) ≤ s := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hks : k ≤ s := by exact_mod_cast hksR
  have henv : 30*(envelope v)^2*Real.log (8*envelope v) ≤ Real.exp v :=
    by simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos v)).mp hv
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg s) hsenv 2
  have hlog : Real.log (8*(s : ℝ)) ≤ Real.log (8*envelope v) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hsenv (by norm_num))
  have hlog0 : 0 ≤ Real.log (8*(s : ℝ)) := Real.log_nonneg (by linarith)
  have hS := (mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 30))
    hlog hlog0 (by positivity)).trans henv
  have hm := mul_le_mul_of_nonneg_right hsep
    (show 0 ≤ 30*(s : ℝ)*Real.log (8*(s : ℝ)) by positivity)
  have hbound : 5*(s : ℝ)*Real.log (8*(s : ℝ)) ≤ Real.exp v/(48*(k : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 48*(k : ℝ)^2)).mpr
    nlinarith only [hm, hS]
  exact (cost_le_exp hs hks).trans (Real.exp_le_exp.mpr hbound)

end NField.Alignment.KaratsubaSourceCost
