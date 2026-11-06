/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteEulerMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Finite Euler bounds for variable reciprocal-divisor exponents -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.NearOneDivisorEuler
open scoped BigOperators Classical

def powerWeight (r : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n=0 then 0 else (n : ℝ)^r
  map_zero' := by simp

/-- Real powers on positive integers give a multiplicative arithmetic function. -/
theorem powerWeight_multiplicative (r : ℝ) : (powerWeight r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [powerWeight]
  · intro m n hm hn hc
    simp only [powerWeight, ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn, ite_false, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- The exact finite divisor-power Euler product reuses the established multiplicative divisor identity. -/
theorem divisor_power_euler {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (∑ d ∈ n.divisors, (d : ℝ)^r) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p+1), ((p : ℝ)^r)^j := by
  calc
    _ = ∑ d ∈ n.divisors, powerWeight r d := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [powerWeight, (Nat.pos_of_mem_divisors hd).ne']
    _ = ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p+1), powerWeight r (p^j) :=
      CollisionFiniteEulerMoments.multiplicative_divisor_euler _ (powerWeight_multiplicative r) hn.ne'
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      simp only [powerWeight, ArithmeticFunction.coe_mk, pow_ne_zero j hp0, ite_false, Nat.cast_pow]
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (j : ℝ) r,
        Real.rpow_mul_natCast (Nat.cast_nonneg p)]

/-- Each finite nonnegative geometric sum lies below its infinite geometric majorant. -/
theorem geometric_sum_le_inverse {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, t^j) ≤ (1-t)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-t)).mpr
  rw [geom_sum_mul_neg]
  have hh := pow_nonneg ht N
  linarith

/-- A uniform local factor bound avoids an unproved infinite product. -/
theorem inverse_one_sub_le_exp {t : ℝ} (ht : 0 ≤ t) (hmax : t ≤ 3/4) :
    (1-t)⁻¹ ≤ Real.exp (4*t) := by
  have hd : 0 < 1-t := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hd).mpr
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (4*t)) hd.le
  have hp : 0 ≤ t*(3-4*t) := mul_nonneg ht (by linarith)
  nlinarith

/-- A finite reciprocal-power divisor sum is bounded by its actual prime-factor exponential. -/
theorem divisor_power_sum_le_exp {n : ℕ} (hn : 0 < n) (r : ℝ)
    (hmax : ∀ p ∈ n.primeFactors, (p : ℝ)^r ≤ 3/4) :
    (∑ d ∈ n.divisors, (d : ℝ)^r) ≤ Real.exp (4*∑ p ∈ n.primeFactors, (p : ℝ)^r) := by
  rw [divisor_power_euler hn r]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (1-(p : ℝ)^r)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Finset.sum_nonneg (fun j hj => pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) r) j)
      · intro p hp
        exact geometric_sum_le_inverse (Real.rpow_nonneg (Nat.cast_nonneg p) r) (by have := hmax p hp; linarith) _
    _ ≤ ∏ p ∈ n.primeFactors, Real.exp (4*(p : ℝ)^r) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hh := hmax p hp
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact inverse_one_sub_le_exp (Real.rpow_nonneg (Nat.cast_nonneg p) r) (hmax p hp)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

end NField.Alignment.NearOneDivisorEuler
