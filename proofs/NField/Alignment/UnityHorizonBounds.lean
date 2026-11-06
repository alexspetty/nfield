/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityDetectorHorizon

/-! # Exact logarithmic horizon bounds and conditional shallow eligibility -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityHorizonBounds
open UnityNativeHilbert UnityNativeProjection UnityPrescribedDetectors UnityDetectorHorizon

/-- Title: `Exact two-sided power bounds for the intrinsic shallow horizon`.

 The literal two-sided dyadic horizon bound uses only the actual positive native deficit. -/
theorem horizon_power_bounds (N : ℕ) :
    4/deficit N≤(2:ℝ)^(horizon N) ∧ (2:ℝ)^(horizon N)<8/deficit N := by
  have hD := deficit_pos N
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log (4/deficit N)/Real.log 2 := by linarith [horizon_ratio_ge_two N]
  constructor
  · apply (Real.log_le_log_iff (div_pos (by norm_num) hD) (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log (4/deficit N)/Real.log 2))
  · apply (Real.log_lt_log_iff (by positivity) (div_pos (by norm_num) hD)).mp
    rw [Real.log_pow, show 8/deficit N=2*(4/deficit N) from by ring,
      Real.log_mul (by norm_num) (ne_of_gt (div_pos (by norm_num) hD))]
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hq) hl
    rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at h
    unfold horizon
    linarith

/-- Title: `The intrinsic horizon leaves at most one quarter of the deficit in tail mass`. -/
theorem horizon_tail_bound (N : ℕ) : (1/2:ℝ)^(horizon N)≤deficit N/4 := by
  have h := (div_le_iff₀ (deficit_pos N)).mp (horizon_power_bounds N).1
  have hp : 0<(2:ℝ)^(horizon N) := by positivity
  rw [div_pow, one_pow]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem shallow_scale_bound (N h : ℕ) (hh : h<horizon N) :
    (2:ℝ)^h<4/deficit N := by
  have hp : (2:ℝ)^(h+1)≤(2:ℝ)^(horizon N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  have hu := (horizon_power_bounds N).2
  have hd := deficit_pos N
  have he : 8/deficit N=2*(4/deficit N) := by ring
  rw [he] at hu
  nlinarith

/-- Title: `Every shallow coarse cutoff obeys the printed native lower bound`.

 Every shallow coarse cutoff satisfies the printed lower bound. -/
theorem shallow_coarseCutoff_lower (N h : ℕ) (hh : h<horizon N) :
    (N:ℝ)*deficit N/4-1<(coarseCutoff N h:ℝ) := by
  have hp : 0<2^h := by positivity
  have hpR : (0:ℝ)<((2^h:ℕ):ℝ) := by exact_mod_cast hp
  have hs := (lt_div_iff₀ (deficit_pos N)).mp (shallow_scale_bound N h hh)
  have hn : (0:ℝ)≤N := Nat.cast_nonneg N
  have hd := mul_le_mul_of_nonneg_left hs.le hn
  have hratio : (N:ℝ)*deficit N/4≤(N:ℝ)/((2^h:ℕ):ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    push_cast at hd ⊢
    nlinarith
  have hdiv : N<2^h*(N/2^h+1) := Nat.lt_mul_div_succ N hp
  have hreal : (N:ℝ)<((2^h:ℕ):ℝ)*((N/2^h:ℕ)+1) := by exact_mod_cast hdiv
  have hf := (div_lt_iff₀ hpR).mpr (by nlinarith : (N:ℝ)<((N/2^h:ℕ)+1)*((2^h:ℕ):ℝ))
  change _<((N/2^h:ℕ):ℝ)
  linarith

/-- Title: `The stated native size condition admits every shallow depth`.

 The stated native size condition admits every shallow depth. -/
theorem eligible_eq_range_of_size (N : ℕ) (hsize : 8≤(N:ℝ)*deficit N) :
    eligible N=Finset.range (horizon N) := by
  apply Finset.filter_eq_self.mpr
  intro h hh
  have hl := shallow_coarseCutoff_lower N h (Finset.mem_range.mp hh)
  have hreal : (1:ℝ)<coarseCutoff N h := by linarith
  have hnat : 1<coarseCutoff N h := by exact_mod_cast hreal
  omega

end NField.Alignment.UnityHorizonBounds
