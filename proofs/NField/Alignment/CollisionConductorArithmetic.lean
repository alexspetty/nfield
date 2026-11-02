/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSquarefreeEuler

/-!
# The finite arithmetic factors of the uniform conductor expansion

The totient and logarithmic factors are explicit prime products and sums.
Differentiating a finite Mobius Euler identity proves the logarithmic
divisor identity without any infinite-series or asymptotic assumption.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorArithmetic

open scoped BigOperators Classical
open ArithmeticFunction CollisionAmplitudeArithmetic CollisionSquarefreeEuler

def totientRatio (q : ℕ) : ℝ := (q.totient : ℝ)/(q : ℝ)
def rho (q : ℕ) : ℝ := totientRatio q/deltaThree q
def nu (q : ℕ) : ℝ := ∑ p ∈ q.primeFactors, Real.log p/((p : ℝ)-1)

theorem totientRatio_euler_product {q : ℕ} (hq : q≠0) :
    totientRatio q=∏ p ∈ q.primeFactors, (1-(p : ℝ)⁻¹) := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq
  have he : (q.totient : ℝ)=(q : ℝ)*∏ p ∈ q.primeFactors, (1-(p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  rw [totientRatio,he]
  field_simp

theorem moebius_divisor_inverse {q : ℕ} (hq : q≠0) :
    (∑ d ∈ q.divisors, (moebius d : ℝ)/(d : ℝ))=totientRatio q := by
  have he := moebius_power_divisor_product hq (-1)
  simp only [Real.rpow_neg_one,← div_eq_mul_inv] at he
  rw [totientRatio_euler_product hq]
  exact he

theorem moebius_power_term_derivative {d : ℕ} (hd : 0<d) :
    HasDerivAt (fun s : ℝ => (moebius d : ℝ)*(d : ℝ)^s)
      ((moebius d : ℝ)*Real.log d/(d : ℝ)) (-1) := by
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have he := (HasDerivAt.const_rpow hdR (hasDerivAt_id (-1 : ℝ))).const_mul (moebius d : ℝ)
  convert! he using 1
  dsimp
  rw [Real.rpow_neg_one]
  ring

theorem euler_power_term_derivative {p : ℕ} (hp : 0<p) :
    HasDerivAt (fun s : ℝ => 1-(p : ℝ)^s) (-(Real.log p/(p : ℝ))) (-1) := by
  have hpR : 0<(p : ℝ) := by exact_mod_cast hp
  have he := (HasDerivAt.const_rpow hpR (hasDerivAt_id (-1 : ℝ))).const_sub 1
  convert! he using 1
  dsimp
  rw [Real.rpow_neg_one]
  ring

theorem moebius_log_divisor {q : ℕ} (hq : q≠0) :
    (∑ d ∈ q.divisors, (moebius d : ℝ)*Real.log d/(d : ℝ))=-(totientRatio q)*nu q := by
  have hs := HasDerivAt.fun_sum (u := q.divisors)
    (fun d hd => moebius_power_term_derivative (Nat.pos_of_mem_divisors hd))
  have hp := HasDerivAt.fun_finsetProd (u := q.primeFactors)
    (fun p hp => euler_power_term_derivative (Nat.prime_of_mem_primeFactors hp).pos)
  have hefun : (fun s : ℝ => ∑ d ∈ q.divisors, (moebius d : ℝ)*(d : ℝ)^s)=
      (fun s : ℝ => ∏ p ∈ q.primeFactors, (1-(p : ℝ)^s)) :=
    funext (moebius_power_divisor_product hq)
  rw [hefun] at hs
  have he := hs.unique hp
  simp only [Real.rpow_neg_one,smul_eq_mul] at he
  rw [he,nu,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpR : (p : ℝ)≠0 := by linarith
  have hmR : (p : ℝ)-1≠0 := by linarith
  rw [totientRatio_euler_product hq,
    ← Finset.mul_prod_erase q.primeFactors (fun p => 1-(p : ℝ)⁻¹) hp]
  field_simp

theorem rho_euler_product {q : ℕ} (hq : q≠0) :
    rho q=∏ p ∈ q.primeFactors, (p : ℝ)^2/((p : ℝ)^2+(p : ℝ)+1) := by
  rw [rho,totientRatio_euler_product hq,deltaThree,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpR : (p : ℝ)≠0 := by linarith
  have hp3 : (1 : ℝ)<(p : ℝ)^3 := by
    calc
      _ < (2 : ℝ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 3
  have hd : 1-((p : ℝ)^3)⁻¹≠0 := by
    have he := inv_lt_one_of_one_lt₀ hp3
    linarith
  have he : (p : ℝ)^2+(p : ℝ)+1≠0 := by positivity
  apply (div_eq_div_iff hd he).mpr
  field_simp
  ring

end NField.Alignment.CollisionConductorArithmetic
