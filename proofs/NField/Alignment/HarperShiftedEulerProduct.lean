/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothCount
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A uniform bound for the shifted finite Euler product

At sigma=1-1/log y each local factor is compared directly with its value
at one. The logarithm-weighted Mertens sum bounds the total correction by
an absolute constant. No smooth-number estimate is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperShiftedEulerProduct

open scoped BigOperators
open Filter Asymptotics HarperSmoothCount HarperSmoothDivisor CollisionMertensInput

def shift (y : ℝ) : ℝ := 1 - 1 / Real.log y

theorem exp_unit_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ 3 * u := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - u by linarith) hu0 (show 1 - u + u = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith [Real.exp_one_lt_three, mul_nonneg hu0 (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three])]

theorem shift_bounds {y : ℝ} (hy : 2 ≤ Real.log y) : 1/2 ≤ shift y ∧ shift y ≤ 1 := by
  have hl : 0 < Real.log y := by linarith
  have h := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hy)
  unfold shift
  constructor <;> linarith [one_div_pos.mpr hl]

theorem prime_power_bound {p sigma : ℝ} (hp : 2 ≤ p) (hs : 1/2 ≤ sigma) :
    p^(-sigma) ≤ 3/4 := by
  have hp0 : 0 < p := by linarith
  have hpow : (p^(-sigma))^2 ≤ 1/2 := by
    rw [← Real.rpow_mul_natCast hp0.le]
    calc
      _ ≤ p^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
      _ ≤ _ := by simpa only [Real.rpow_neg_one, one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  nlinarith [Real.rpow_nonneg hp0.le (-sigma)]

theorem prime_power_difference {y p : ℝ} (hy : 2 ≤ Real.log y) (hp : 2 ≤ p) (hpy : p ≤ y) :
    p^( -shift y) - p⁻¹ ≤ 3 / Real.log y * (Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 < Real.log y := by linarith
  have hu0 : 0 ≤ Real.log p / Real.log y := div_nonneg (Real.log_nonneg (by linarith)) hl.le
  have hu1 : Real.log p / Real.log y ≤ 1 := (div_le_one hl).mpr (Real.log_le_log hp0 hpy)
  have he : p^(-shift y) = p⁻¹ * Real.exp (Real.log p / Real.log y) := by
    rw [shift, show -(1 - 1 / Real.log y) = (-1 : ℝ) + 1 / Real.log y by ring,
      Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0]
    congr 2
    ring
  rw [he]
  calc
    _ = p⁻¹ * (Real.exp (Real.log p / Real.log y) - 1) := by ring
    _ ≤ p⁻¹ * (3 * (Real.log p / Real.log y)) :=
      mul_le_mul_of_nonneg_left (exp_unit_bound hu0 hu1) (inv_nonneg.mpr hp0.le)
    _ = _ := by ring

theorem factor_ratio_bound {a b D : ℝ} (ha : a ≤ 3/4) (hab : b ≤ a) (hd : a - b ≤ D) :
    (1 - b) / (1 - a) ≤ Real.exp (4 * D) := by
  have hden : 0 < 1 - a := by linarith
  have hinv : (1 - a)⁻¹ ≤ 4 := by rw [inv_eq_one_div, div_le_iff₀ hden]; linarith
  have hD : 0 ≤ D := by linarith
  calc
    _ = 1 + (a - b) * (1 - a)⁻¹ := by field_simp; ring
    _ ≤ 1 + D * 4 := by gcongr
    _ ≤ _ := by linarith [Real.add_one_le_exp (4 * D)]

theorem prime_factor_bound {y : ℝ} (hy : 2 ≤ Real.log y) {p : ℕ} (hp : p ∈ primesUpTo y) :
    (1 - (p : ℝ)^(-shift y))⁻¹ ≤ (1 - (p : ℝ)⁻¹)⁻¹ *
      Real.exp (12 / Real.log y * (Real.log p / p)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hb : (p : ℝ)⁻¹ ≤ (p : ℝ)^(-shift y) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [(shift_bounds hy).2])
  have hb1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hr := factor_ratio_bound (prime_power_bound hpR (shift_bounds hy).1) hb
    (prime_power_difference hy hpR (primesUpTo_mem.mp hp).2)
  have hn : 1 - (p : ℝ)⁻¹ ≠ 0 := by linarith
  calc
    _ = (1 - (p : ℝ)⁻¹)⁻¹ * ((1 - (p : ℝ)⁻¹) / (1 - (p : ℝ)^(-shift y))) := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ * Real.exp (4 * (3 / Real.log y * (Real.log p / p))) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by congr 2; ring

theorem shiftedProduct_bound {y : ℝ} (hy : 2 ≤ Real.log y) :
    shiftedProduct y (shift y) ≤ inversePrimeProduct y *
      Real.exp (12 / Real.log y * logPrimeSum y) := by
  calc
    _ ≤ ∏ p ∈ primesUpTo y, (1 - (p : ℝ)⁻¹)⁻¹ *
        Real.exp (12 / Real.log y * (Real.log p / p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h := prime_power_bound (show (2 : ℝ) ≤ p by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le)
          (shift_bounds hy).1
        exact inv_nonneg.mpr (by linarith)
      · exact fun p hp => prime_factor_bound hy hp
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      rfl

theorem eventual_shiftedProduct_bound : ∀ᶠ y : ℝ in atTop,
    shiftedProduct y (shift y) ≤ Real.exp 24 * inversePrimeProduct y := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 4 + 4),
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with y hy hl htwo
  have hsum := (abs_le.mp (logPrimeSum_error_bound hy)).2
  have hL : 0 < Real.log y := by linarith
  have he : 12 / Real.log y * logPrimeSum y ≤ 24 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL).mpr
    nlinarith
  calc
    _ ≤ inversePrimeProduct y * Real.exp (12 / Real.log y * logPrimeSum y) := shiftedProduct_bound htwo
    _ ≤ inversePrimeProduct y * Real.exp 24 := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr he) (inversePrimeProduct_pos y).le
    _ = _ := mul_comm _ _

theorem eventual_shiftedProduct_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
    shiftedProduct y (shift y) ≤ C * Real.log y := by
  obtain ⟨C, hC, hprod⟩ := uniform_smooth_divisor_estimate
  refine ⟨Real.exp 24 * C, by positivity, ?_⟩
  filter_upwards [eventual_shiftedProduct_bound, hprod] with y hy hp
  have h := (hp 1 (by norm_num)).2
  norm_num at h
  calc
    _ ≤ Real.exp 24 * inversePrimeProduct y := hy
    _ ≤ Real.exp 24 * (C * Real.log y) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by ring

end NField.Alignment.HarperShiftedEulerProduct
