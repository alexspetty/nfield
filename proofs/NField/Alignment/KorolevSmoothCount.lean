/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothCountDecay

/-!
# Smooth-number removal at Korolev's cutoff

Korolev's Lemma A removes integers whose prime factors are all at most
Q = exp(log x / log(log x)). The earlier Harper count at this same Q
is only O(x/log(log x)). A fixed shift of two in the existing Rankin
argument gives the stronger O(x/(log x * log(log x))) estimate.
The Mertens theorem, Euler product, Rankin inequality, and cutoff limits
are reused. This proves only the smooth-number removal component;
Korolev's short exponential-sum estimate remains open.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSmoothCount
open scoped BigOperators Topology
open Filter HarperSmoothCount HarperSmoothDivisor CollisionMertensInput
  HarperShiftedEulerProduct HarperRoundedCutoff HarperSmoothCountDecay

def shiftTwo (y : ℝ) : ℝ := 1 - 2 / Real.log y

theorem shiftTwo_bounds {y : ℝ} (hy : 4 ≤ Real.log y) :
    1/2 ≤ shiftTwo y ∧ shiftTwo y ≤ 1 := by
  have hl : 0 < Real.log y := by linarith
  have h : 2 / Real.log y ≤ 1/2 := (div_le_iff₀ hl).mpr (by linarith)
  unfold shiftTwo
  constructor <;> linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl.le]

/-- Convexity on [0,2], retaining a harmless absolute constant. -/
theorem exp_two_unit_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (2*u) - 1 ≤ Real.exp 2 * u := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (2 : ℝ))
    (show 0 ≤ 1-u by linarith) hu0 (show 1-u+u=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm u 2] at h
  nlinarith

theorem prime_power_difference_two {y p : ℝ} (hy : 4 ≤ Real.log y)
    (hp : 2 ≤ p) (hpy : p ≤ y) :
    p^(-shiftTwo y) - p⁻¹ ≤ Real.exp 2 / Real.log y * (Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 < Real.log y := by linarith
  have hu0 : 0 ≤ Real.log p / Real.log y :=
    div_nonneg (Real.log_nonneg (by linarith)) hl.le
  have hu1 : Real.log p / Real.log y ≤ 1 :=
    (div_le_one hl).mpr (Real.log_le_log hp0 hpy)
  have he : p^(-shiftTwo y) = p⁻¹ * Real.exp (2*(Real.log p / Real.log y)) := by
    rw [shiftTwo, show -(1-2/Real.log y)=(-1:ℝ)+2/Real.log y by ring,
      Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0]
    congr 2
    ring
  rw [he]
  calc
    _ = p⁻¹ * (Real.exp (2*(Real.log p / Real.log y))-1) := by ring
    _ ≤ p⁻¹ * (Real.exp 2 * (Real.log p / Real.log y)) :=
      mul_le_mul_of_nonneg_left (exp_two_unit_bound hu0 hu1) (inv_nonneg.mpr hp0.le)
    _ = _ := by ring

theorem prime_factor_bound_two {y : ℝ} (hy : 4 ≤ Real.log y)
    {p : ℕ} (hp : p ∈ primesUpTo y) :
    (1-(p:ℝ)^(-shiftTwo y))⁻¹ ≤ (1-(p:ℝ)⁻¹)⁻¹ *
      Real.exp (4*Real.exp 2 / Real.log y * (Real.log p / p)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le
  have hb : (p:ℝ)⁻¹ ≤ (p:ℝ)^(-shiftTwo y) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [(shiftTwo_bounds hy).2])
  have hb1 : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hr := factor_ratio_bound (prime_power_bound hpR (shiftTwo_bounds hy).1) hb
    (prime_power_difference_two hy hpR (primesUpTo_mem.mp hp).2)
  have hn : 1-(p:ℝ)⁻¹ ≠ 0 := by linarith
  calc
    _ = (1-(p:ℝ)⁻¹)⁻¹ * ((1-(p:ℝ)⁻¹)/(1-(p:ℝ)^(-shiftTwo y))) := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ ≤ (1-(p:ℝ)⁻¹)⁻¹ *
        Real.exp (4*(Real.exp 2/Real.log y*(Real.log p/p))) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by congr 2; ring

theorem shiftedProduct_two_bound {y : ℝ} (hy : 4 ≤ Real.log y) :
    shiftedProduct y (shiftTwo y) ≤ inversePrimeProduct y *
      Real.exp (4*Real.exp 2 / Real.log y * logPrimeSum y) := by
  calc
    _ ≤ ∏ p ∈ primesUpTo y, (1-(p:ℝ)⁻¹)⁻¹ *
        Real.exp (4*Real.exp 2 / Real.log y * (Real.log p/p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h := prime_power_bound
          (show (2:ℝ) ≤ p by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le)
          (shiftTwo_bounds hy).1
        exact inv_nonneg.mpr (by linarith)
      · exact fun p hp => prime_factor_bound_two hy hp
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      rfl

theorem eventual_shiftedProduct_two_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
      shiftedProduct y (shiftTwo y) ≤ C*Real.log y := by
  obtain ⟨C, hC, hprod⟩ := uniform_smooth_divisor_estimate
  refine ⟨Real.exp (8*Real.exp 2)*C, by positivity, ?_⟩
  filter_upwards [hprod, eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 4+4),
    Real.tendsto_log_atTop.eventually_ge_atTop 4] with y hp hy hl hfour
  have hsum := (abs_le.mp (logPrimeSum_error_bound hy)).2
  have hL : 0 < Real.log y := by linarith
  have hratio : logPrimeSum y / Real.log y ≤ 2 :=
    (div_le_iff₀ hL).mpr (by linarith)
  have he : 4*Real.exp 2/Real.log y*logPrimeSum y ≤ 8*Real.exp 2 := by
    calc
      _ = (4*Real.exp 2)*(logPrimeSum y/Real.log y) := by ring
      _ ≤ (4*Real.exp 2)*2 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hb := (hp 1 (by norm_num)).2
  norm_num at hb
  calc
    _ ≤ inversePrimeProduct y * Real.exp (4*Real.exp 2/Real.log y*logPrimeSum y) :=
      shiftedProduct_two_bound hfour
    _ ≤ inversePrimeProduct y * Real.exp (8*Real.exp 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (inversePrimeProduct_pos y).le
    _ ≤ (C*Real.log y)*Real.exp (8*Real.exp 2) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by ring

/-- The previous cutoff is exactly the one in Korolev's Lemma A. -/
theorem smoothCutoff_eq_exp {x : ℝ} (hx : 0 < x) :
    smoothCutoff x = Real.exp (Real.log x / Real.log (Real.log x)) := by
  rw [smoothCutoff, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem rankin_scale_two_identity {x : ℝ} (hx : 1 < x)
    (hu : 0 < Real.log (Real.log x)) :
    x^(shiftTwo (smoothCutoff x))*Real.log (smoothCutoff x) =
      x/(Real.log x*Real.log (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have he : x^(2/Real.log (smoothCutoff x)) = (Real.log x)^2 := by
    rw [Real.rpow_def_of_pos hx0, log_smoothCutoff hx0]
    have harg : Real.log x*(2/(Real.log x/Real.log (Real.log x))) =
        Real.log (Real.log x)+Real.log (Real.log x) := by field_simp; ring
    rw [harg, Real.exp_add, Real.exp_log hl]
    ring
  rw [shiftTwo, Real.rpow_sub hx0, Real.rpow_one, he, log_smoothCutoff hx0]
  field_simp

/-- Actual smooth-number count, stronger than the bound needed at the
first smooth-number removal in Korolev's Lemma A. -/
theorem eventual_smoothCount_two_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      smoothCount x (smoothCutoff x) ≤ C*(x/(Real.log x*Real.log (Real.log x))) := by
  obtain ⟨C, hC, hp⟩ := eventual_shiftedProduct_two_log_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [smoothCutoff_tendsto.eventually hp,
    (Real.tendsto_log_atTop.comp smoothCutoff_tendsto).eventually_ge_atTop 4,
    eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x hprod hy hx hu
  dsimp only [Function.comp_apply] at hy hu
  have hs : 0 < shiftTwo (smoothCutoff x) := by linarith [(shiftTwo_bounds hy).1]
  calc
    _ ≤ x^(shiftTwo (smoothCutoff x))*shiftedProduct (smoothCutoff x) (shiftTwo (smoothCutoff x)) :=
      rankin_bound (by linarith) _ hs
    _ ≤ x^(shiftTwo (smoothCutoff x))*(C*Real.log (smoothCutoff x)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C*(x^(shiftTwo (smoothCutoff x))*Real.log (smoothCutoff x)) := by ring
    _ = _ := by rw [rankin_scale_two_identity hx hu]

end NField.Alignment.KorolevSmoothCount
