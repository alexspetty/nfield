/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPolynomialMeanValue

/-! # Taking the two moment roots with an absolute constant -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealPolynomialExponentialBound
open scoped BigOperators
open RealPolynomialMomentBox RealKernelSaving RealPolynomialMeanValue
  VinogradovNormalizedRecurrence VinogradovMeanValue

theorem degree_cost_bound (n s : ℕ) (hs : 1 ≤ s) (hns : n ≤ s) :
    (1000:ℝ)^n*(s:ℝ)^(4*n) ≤ Real.exp (1008*(s:ℝ)^2) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hnsR : (n:ℝ) ≤ s := by exact_mod_cast hns
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hlogS := Real.log_le_self hs0.le
  have hlogC := Real.log_le_self (by norm_num : (0:ℝ) ≤ 1000)
  have he₁ : (1000:ℝ)^n = Real.exp ((n:ℝ)*Real.log 1000) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<1000)]
  have he₂ : (s:ℝ)^(4*n) = Real.exp ((4*n:ℕ)*Real.log (s:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hs0]
  rw [he₁,he₂,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hc := mul_le_mul_of_nonneg_left hlogC hn0
  have hs' := mul_le_mul_of_nonneg_left hlogS (show 0 ≤ 4*(n:ℝ) by positivity)
  nlinarith [mul_nonneg (show 0 ≤ (s:ℝ)-n by linarith) hs0.le]

theorem moment_root_bound (u H A E : ℝ) (s : ℕ) (hH : 0 ≤ H) (hs : 1 ≤ s)
    (hbound : u^(8*s^2) ≤ H^(16*s^2)*Real.exp ((4*A+1008)*(s:ℝ)^2+E)) :
    u ≤ H^2*Real.exp (A/2+126+E/(8*(s:ℝ)^2)) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  apply le_of_pow_le_pow_left₀ (show 8*s^2 ≠ 0 by positivity) (by positivity)
  apply hbound.trans_eq
  rw [mul_pow,← pow_mul,← Real.exp_nat_mul]
  have he : (2:ℕ)*(8*s^2) = 16*s^2 := by ring
  rw [he]
  congr 1
  congr 1
  push_cast
  field_simp
  ring

theorem polynomial_exponential_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (n s H : ℕ) (β : Fin n → ℝ) (T : ℝ),
      2 ≤ n → n^2 ≤ s → 1 ≤ H → (∀ j, β j ≠ 0) →
      (∏ j : Fin n, saving (β j) (s*H^(j.val+1))) ≤ Real.exp (-T) →
      ‖polynomialBilinear β H‖ ≤ (H:ℝ)^2*Real.exp (A/2+126+
        (4*((n:ℝ)^2*Real.exp 2*Real.exp (-(s:ℝ)/(n:ℝ)^2))*Real.log (H:ℝ)-T)/
          (8*(s:ℝ)^2)) := by
  obtain ⟨A,hA,hmean⟩ := uniform_normalized_mean_value
  refine ⟨A,hA,?_⟩
  intro n s H β T hn hs hH hβ hprod
  have hs1 : 1 ≤ s := by nlinarith
  have hns : n ≤ s := by nlinarith
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  let δ := (n:ℝ)^2*Real.exp 2*Real.exp (-(s:ℝ)/(n:ℝ)^2)
  have hm := hmean n s H hn hs hH
  have hm' : mean s n H ≤ Real.exp (A*(s:ℝ)^2+δ*Real.log (H:ℝ)) := by
    have hr : (H:ℝ)^δ = Real.exp (δ*Real.log (H:ℝ)) := by
      rw [Real.rpow_def_of_pos hH0]
      congr 1
      ring
    change mean s n H+1 ≤ Real.exp (A*(s:ℝ)^2)*(H:ℝ)^δ at hm
    rw [hr,← Real.exp_add] at hm
    linarith
  have hm4 := pow_le_pow_left₀ (mean_nonneg s n H) hm' 4
  rw [← Real.exp_nat_mul] at hm4
  have hc := degree_cost_bound n s hs1 hns
  have hraw := polynomial_normalized_moment_bound β hβ H s hs1 hH
    ((weight_le_sq (by omega)).trans (by omega))
  apply moment_root_bound _ (H:ℝ) A _ s hH0.le hs1
  calc
    _ ≤ 1000^n*(s:ℝ)^(4*n)*(H:ℝ)^(16*s^2)*(mean s n H)^4*
        ∏ j : Fin n, saving (β j) (s*H^(j.val+1)) := hraw
    _ ≤ Real.exp (1008*(s:ℝ)^2)*(H:ℝ)^(16*s^2)*
        Real.exp (4*(A*(s:ℝ)^2+δ*Real.log (H:ℝ)))*Real.exp (-T) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hc (by positivity)
        · exact hm4
        · positivity
        · positivity
      · exact hprod
      · exact Finset.prod_nonneg (fun j _ => saving_nonneg _ _)
      · positivity
    _ = _ := by
      calc
        _ = (H:ℝ)^(16*s^2)*(Real.exp (1008*(s:ℝ)^2)*
            Real.exp (4*(A*(s:ℝ)^2+δ*Real.log (H:ℝ)))*Real.exp (-T)) := by ring
        _ = _ := by
          rw [← Real.exp_add,← Real.exp_add]
          congr 2
          dsimp [δ]
          ring

end NField.Alignment.RealPolynomialExponentialBound
