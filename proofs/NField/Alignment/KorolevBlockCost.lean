/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceCost

/-! # Factorial and logarithmic population costs for actual prime blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevBlockCost
open KorolevSourceEnvelope KaratsubaSourceCost Filter
open scoped Topology

def cost (L : ℝ) (k s : ℕ) : ℝ :=
  (k.factorial : ℝ)*(s.factorial : ℝ)*(s : ℝ)*4^s*(4*L)^(k+s)

theorem cost_le_power {L : ℝ} {k s : ℕ} (hL : 1 ≤ L) (hs : 1 ≤ s)
    (hks : k ≤ s) (hsL : (s : ℝ) ≤ L) : cost L k s ≤ (4*L)^(6*s) := by
  have hkS : (k : ℝ) ≤ s := by exact_mod_cast hks
  have hkR : (k : ℝ) ≤ L := hkS.trans hsL
  have hfK : (k.factorial : ℝ) ≤ (4*L)^k := by
    have hh : (k.factorial : ℝ) ≤ (k : ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
    exact hh.trans (pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) k)
  have hfS : (s.factorial : ℝ) ≤ (4*L)^s := by
    have hh : (s.factorial : ℝ) ≤ (s : ℝ)^s := by exact_mod_cast Nat.factorial_le_pow s
    exact hh.trans (pow_le_pow_left₀ (Nat.cast_nonneg s) (by linarith) s)
  have hp : (4 : ℝ)^s ≤ (4*L)^s := pow_le_pow_left₀ (by norm_num) (by linarith) s
  unfold cost
  calc
    _ ≤ (4*L)^k*(4*L)^s*(4*L)*(4*L)^s*(4*L)^(k+s) := by
      gcongr
      linarith
    _ = (4*L)^k*(4*L)^s*(4*L)^1*(4*L)^s*(4*L)^(k+s) := by rw [pow_one]
    _ = (4*L)^(2*k+3*s+1) := by
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ 4*L) (by omega : 2*k+3*s+1 ≤ 6*s)

theorem cost_le_exp {L : ℝ} {k s : ℕ} (hL : 1 ≤ L) (hs : 1 ≤ s)
    (hks : k ≤ s) (hsL : (s : ℝ) ≤ L) :
    cost L k s ≤ Real.exp (6*(s : ℝ)*Real.log (4*L)) := by
  have he : Real.exp (6*(s : ℝ)*Real.log (4*L)) = (4*L)^(6*s) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.exp_log (by linarith : 0 < 4*L)] using
      Real.exp_nat_mul (Real.log (4*L)) (6*s)
  rw [he]
  exact cost_le_power hL hs hks hsL

theorem envelope_population_cost_tendsto :
    Tendsto (fun v : ℝ => 96*(envelope v)^2*(v+Real.log 4)/Real.exp v) atTop (𝓝 0) := by
  have ht := (envelope_log_ratio_tendsto.const_mul (192/25 : ℝ)).add
    (envelope_square_ratio_tendsto.const_mul (96*(Real.log 4-(12/5)*Real.log 32)))
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun v => by dsimp only; rw [log_eight_envelope]; ring)

theorem eventual_cost_absorbed : ∀ᶠ v : ℝ in atTop,
    ∀ k s : ℕ, 1 ≤ k → 1 ≤ s → 8*(k : ℝ)^2 ≤ s → (s : ℝ) ≤ envelope v →
      cost (Real.exp v) k s ≤ Real.exp (Real.exp v/(128*(k : ℝ)^2)) := by
  filter_upwards [envelope_population_cost_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventual_envelope_small 1, eventually_ge_atTop (0 : ℝ)] with v hv he hv0 k s hk hs hsep hsenv
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hksR : (k : ℝ) ≤ s := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hks : k ≤ s := by exact_mod_cast hksR
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg s) hsenv 2
  have henv : (envelope v)^2 ≤ Real.exp v := by simpa using (div_le_iff₀ (Real.exp_pos v)).mp he
  have hsL : (s : ℝ) ≤ Real.exp v := by nlinarith [sq_nonneg ((s : ℝ)-1)]
  have hL : 1 ≤ Real.exp v := Real.one_le_exp hv0
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hc : 96*(envelope v)^2*(v+Real.log 4) ≤ Real.exp v := by
    simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos v)).mp hv
  have hS : 96*(s : ℝ)^2*(v+Real.log 4) ≤ Real.exp v :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by linarith)).trans hc
  have hm := mul_le_mul_of_nonneg_right hsep
    (show 0 ≤ 96*(s : ℝ)*(v+Real.log 4) by positivity)
  have hbound : 6*(s : ℝ)*Real.log (4*Real.exp v) ≤ Real.exp v/(128*(k : ℝ)^2) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
    apply (le_div_iff₀ (by positivity : 0 < 128*(k : ℝ)^2)).mpr
    nlinarith only [hm, hS]
  exact (cost_le_exp hL hs hks hsL).trans (Real.exp_le_exp.mpr hbound)

end NField.Alignment.KorolevBlockCost
