/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResetLocalFactors

/-!
# A uniform summable majorant along every prime-power tower

For p >= 2 the inverse powers after the first are dominated by powers of
one half. The geometric mass and first moment give one explicit bound
independent of the height of the tower.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimePowerMajorant

theorem half_linear_hasSum (l : ℝ) :
    HasSum (fun j : ℕ => (1+((j : ℝ)+1)*l)*(1/2 : ℝ)^j) (2+4*l) := by
  have h0 : HasSum (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
    convert! hasSum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1) using 1
    norm_num
  have h1 : HasSum (fun j : ℕ => (j : ℝ)*(1/2 : ℝ)^j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one
      (by norm_num : ‖(1/2 : ℝ)‖ < 1) using 1
    norm_num
  have h := h0.add ((h1.add h0).mul_left l)
  convert! h using 1
  · funext j
    ring
  · ring

theorem prime_power_term_majorant {p : ℝ} (hp : 2 ≤ p) (j : ℕ) :
    (1+((j : ℝ)+1)*Real.log p)/p^(j+1) ≤
      ((1+((j : ℝ)+1)*Real.log p)*(1/2 : ℝ)^j)/p := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr : p⁻¹ ≤ (1/2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hp0.le) hr j
  have hc : 0 ≤ (1+((j : ℝ)+1)*Real.log p)/p := by positivity
  have h := mul_le_mul_of_nonneg_left hpow hc
  convert! h using 1 <;> simp only [div_eq_mul_inv,inv_pow,pow_succ] <;> ring

theorem prime_power_majorant_sum {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    (∑ j ∈ Finset.range v, (1+((j : ℝ)+1)*Real.log p)/p^(j+1)) ≤
      4*(1+Real.log p)/p := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hsum := (half_linear_hasSum (Real.log p)).summable.sum_le_tsum (Finset.range v)
    (fun j hj => by positivity)
  rw [(half_linear_hasSum (Real.log p)).tsum_eq] at hsum
  calc
    _ ≤ ∑ j ∈ Finset.range v, ((1+((j : ℝ)+1)*Real.log p)*(1/2 : ℝ)^j)/p :=
      Finset.sum_le_sum (fun j hj => prime_power_term_majorant hp j)
    _ = (∑ j ∈ Finset.range v, (1+((j : ℝ)+1)*Real.log p)*(1/2 : ℝ)^j)/p := by
      rw [Finset.sum_div]
    _ ≤ (2+4*Real.log p)/p := div_le_div_of_nonneg_right hsum hp0.le
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hp0.le

end NField.Alignment.CollisionPrimePowerMajorant
