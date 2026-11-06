/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityDetectorResponse

/-! # The actual orthonormal unity spine in the native observation space -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySpineBasis
open scoped BigOperators
open UnityNativeWeights UnityNativeHilbert UnityNativeCopies UnityNativeDilation UnityNativeIsometry

def spine (h : ℕ) : NativeHilbert := scaledCopy (2^h) (by positivity) rootDetail

theorem spine_eq_iterate (h : ℕ) : spine h=(binaryCopy^[h]) rootDetail :=
  (binary_iterate h rootDetail).symm

theorem spine_norm (h : ℕ) : ‖spine h‖=1 := by
  rw [spine, LinearIsometry.norm_map, rootDetail_norm]

theorem spine_add (h k : ℕ) :
    spine (h+k)=scaledCopy (2^h) (by positivity) (spine k) := by
  simp only [spine, scaledCopy_comp, pow_add]

theorem root_spine_inner_zero {h : ℕ} (hh : 0<h) : inner ℝ rootDetail (spine h)=0 := by
  have hp : 1<2^h := by
    have hs : 2≤2^h := Nat.pow_le_pow_right (by omega : 1≤2) hh
    omega
  have hv : value (spine h) 1=0 := by
    rw [spine, scaledCopy_value, Nat.div_eq_of_lt hp, value_zero, mul_zero]
  have hc : spine h 0=0 := by
    rw [← coordinate_value (spine h) 0]
    simpa only [Nat.zero_add, hv, mul_zero]
  simp only [rootDetail, lp.inner_single_left, hc, inner_zero_right]

theorem spine_inner_of_lt {h k : ℕ} (hhk : h<k) : inner ℝ (spine h) (spine k)=0 := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hhk.le
  have hd0 : 0<d := by omega
  rw [hd, spine_add]
  change inner ℝ (scaledCopy (2^h) (by positivity) rootDetail)
    (scaledCopy (2^h) (by positivity) (spine d))=0
  rw [LinearIsometry.inner_map_map]
  exact root_spine_inner_zero hd0

/-- Title: `The actual copied root details form an orthonormal spine`. -/
theorem spine_orthonormal : Orthonormal ℝ spine := by
  refine ⟨spine_norm, ?_⟩
  intro h k hhk
  rcases lt_or_gt_of_ne hhk with hlt|hlt
  · exact spine_inner_of_lt hlt
  · rw [real_inner_comm]
    exact spine_inner_of_lt hlt

def ratio : ℝ := (Real.sqrt 2)⁻¹
def coefficient (h : ℕ) : ℝ := ratio^(h+1)

theorem ratio_pos : 0<ratio := by unfold ratio; positivity
theorem ratio_sq : ratio^2=(1/2:ℝ) := by
  rw [ratio, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num
theorem ratio_lt_one : ratio<1 := by
  have h := ratio_sq
  nlinarith [ratio_pos]

theorem sqrt_two_power (h : ℕ) : Real.sqrt ((2^h : ℕ):ℝ)=(Real.sqrt 2)^h := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ih, pow_succ]
    norm_num

theorem coefficient_sq (h : ℕ) : (coefficient h)^2=(1/2:ℝ)^(h+1) := by
  rw [coefficient, ← pow_mul, Nat.mul_comm, pow_mul, ratio_sq]

/-- Title: `Exact energy of the finite unity-spine coefficients`. -/
theorem coefficient_sq_sum (H : ℕ) :
    (∑ h∈Finset.range H, (coefficient h)^2)=1-(1/2:ℝ)^H := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih, coefficient_sq, pow_succ]
    ring

theorem binary_boundary_root : boundary 2 (by omega)=ratio • rootDetail := by
  apply ext_value
  intro m hm
  rw [boundary_value _ _ hm, value_smul, rootDetail_value hm]
  by_cases h : m=1
  · subst m
    norm_num [ratio, Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)]
  · have hn : ¬m<2 := by omega
    simp only [if_neg hn, if_neg h, mul_zero]

/-- Title: `Each unity-spine term is an exact copied boundary block`.

 Each spine term is the exact copied first boundary block. -/
theorem copied_boundary_spine (h : ℕ) :
    copy (2^h) (by positivity) (boundary 2 (by omega))=coefficient h • spine h := by
  rw [binary_boundary_root, copy_smul]
  change ratio • copy (2^h) (by positivity) rootDetail=
    coefficient h • (Real.sqrt ((2^h : ℕ):ℝ) • copy (2^h) (by positivity) rootDetail)
  rw [smul_smul, sqrt_two_power]
  congr 1
  rw [coefficient, pow_succ, ratio, inv_pow]
  have hp : (Real.sqrt 2)^h≠0 := pow_ne_zero _ (Real.sqrt_ne_zero'.mpr (by norm_num))
  field_simp

def tail (H : ℕ) : NativeHilbert := copy (2^H) (by positivity) unity
def head (H : ℕ) : NativeHilbert := ∑ h∈Finset.range H, coefficient h • spine h

theorem tail_step (H : ℕ) : tail H=coefficient H • spine H+tail (H+1) := by
  have h := congrArg (copy (2^H) (by positivity)) (unity_boundary_copy 2 (by omega))
  rw [copy_add, copied_boundary_spine, copy_copy] at h
  simpa only [tail, pow_succ] using h

/-- Title: `The finite unity spine retains its complete copied tail`.

 The finite unity spine retains its exact copied tail. -/
theorem head_add_tail (H : ℕ) : head H+tail H=unity := by
  induction H with
  | zero => simp [head, tail, copy_one]
  | succ H ih =>
    rw [head, Finset.sum_range_succ]
    change (head H+coefficient H • spine H)+tail (H+1)=unity
    rw [add_assoc, ← tail_step, ih]

theorem head_eq_unity_sub_tail (H : ℕ) : head H=unity-tail H :=
  eq_sub_iff_add_eq.mpr (head_add_tail H)

/-- Title: `Exact native energy of the complete spine tail`. -/
theorem tail_norm_sq (H : ℕ) : ‖tail H‖^2=(1/2:ℝ)^H := by
  rw [tail, copy_norm_sq, unity_norm_sq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]

/-- Title: `Exact native energy of the shallow unity head`. -/
theorem head_norm_sq (H : ℕ) : ‖head H‖^2=1-(1/2:ℝ)^H := by
  rw [← real_inner_self_eq_norm_sq, head, spine_orthonormal.inner_sum]
  simpa only [conj_trivial, ← sq] using coefficient_sq_sum H

theorem unity_tail_inner (H : ℕ) : inner ℝ unity (tail H)=(1/2:ℝ)^H := by
  rw [tail, copy_mean, real_inner_self_eq_norm_sq, unity_norm_sq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]

theorem unity_head_inner (H : ℕ) : inner ℝ unity (head H)=1-(1/2:ℝ)^H := by
  rw [head_eq_unity_sub_tail, inner_sub_right, real_inner_self_eq_norm_sq, unity_norm_sq,
    unity_tail_inner]

end NField.Alignment.UnitySpineBasis
