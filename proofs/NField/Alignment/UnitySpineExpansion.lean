/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitySpineBasis
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Exact native unity expansion and finite-head coefficients -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySpineExpansion
open scoped BigOperators
open Filter Topology
open UnityNativeWeights UnityNativeHilbert UnityNativeCopies UnityNativeDilation UnityNativeIsometry
open UnitySpineBasis

theorem coefficient_pos (h : ℕ) : 0<coefficient h := pow_pos ratio_pos _

theorem unity_root_inner : inner ℝ unity rootDetail=ratio := by
  rw [rootDetail, lp.inner_single_right]
  simp only [RCLike.inner_apply, conj_trivial, one_mul]
  rw [← coordinate_value unity 0, unity_value (by omega)]
  norm_num [weight, ratio, Real.sqrt_div]

/-- Title: `The literal unity-spine readings are the prescribed coefficients`. -/
theorem unity_spine_inner (h : ℕ) : inner ℝ unity (spine h)=coefficient h := by
  have hmean := congrArg (fun f : NativeHilbert => inner ℝ unity f) (copied_boundary_spine h)
  rw [copy_mean, binary_boundary_root, real_inner_smul_right, unity_root_inner,
    real_inner_smul_right] at hmean
  have hs : ratio*ratio/((2^h:ℕ):ℝ)=(coefficient h)^2 := by
    rw [← sq, ratio_sq, coefficient_sq, pow_succ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
    ring
  rw [hs] at hmean
  have hp := coefficient_pos h
  nlinarith

theorem head_spine_inner (H h : ℕ) (hh : h<H) : inner ℝ (head H) (spine h)=coefficient h := by
  rw [real_inner_comm]
  exact spine_orthonormal.inner_right_sum coefficient (Finset.mem_range.mpr hh)

/-- Title: `The complete copied tail is orthogonal to every shallow spine vector`. -/
theorem tail_spine_inner (H h : ℕ) (hh : h<H) : inner ℝ (tail H) (spine h)=0 := by
  have he := congrArg (fun f : NativeHilbert => inner ℝ f (spine h)) (head_add_tail H)
  rw [inner_add_left, head_spine_inner H h hh, unity_spine_inner] at he
  linarith

theorem tail_head_inner (H : ℕ) : inner ℝ (tail H) (head H)=0 := by
  rw [head, inner_sum]
  apply Finset.sum_eq_zero
  intro h hh
  rw [real_inner_smul_right, tail_spine_inner H h (Finset.mem_range.mp hh), mul_zero]

theorem tail_tendsto_zero : Tendsto tail atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have he (H : ℕ) : ‖tail H‖=Real.sqrt ((1/2:ℝ)^H) := by
    rw [← tail_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [he, Real.sqrt_zero] using h.sqrt

theorem head_tendsto_unity : Tendsto head atTop (𝓝 unity) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => unity) atTop (𝓝 unity)).sub tail_tendsto_zero
  simpa only [sub_zero, ← head_eq_unity_sub_tail] using h

/-- Title: `The actual unity expansion converges in the native Hilbert norm`.

 The actual unity expansion converges in the complete native Hilbert norm. -/
theorem unity_spine_hasSum : HasSum (fun h => coefficient h • spine h) unity := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr head_tendsto_unity
  have h := (summable_geometric_of_lt_one ratio_pos.le ratio_lt_one).mul_right ratio
  have hn (h : ℕ) : ‖coefficient h • spine h‖=coefficient h := by
    rw [norm_smul, spine_norm, mul_one, Real.norm_eq_abs, abs_of_pos (coefficient_pos h)]
  simp_rw [hn]
  simpa only [coefficient, pow_succ] using h

theorem unity_spine_tsum : (∑' h, coefficient h • spine h)=unity := unity_spine_hasSum.tsum_eq

/-- Title: `The spine coefficients equal the printed half-power law`. -/
theorem coefficient_rpow (h : ℕ) : coefficient h=(2:ℝ)^(-((h:ℝ)+1)/2) := by
  rw [coefficient, ratio, inv_pow, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by norm_num : (0:ℝ)≤2), ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  congr 1
  push_cast
  ring

end NField.Alignment.UnitySpineExpansion
