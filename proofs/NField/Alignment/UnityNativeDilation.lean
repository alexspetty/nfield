/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeCopies
import NField.Alignment.UnityNativeProjection

/-! # Exact clock dilation and the native boundary correction -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityNativeDilation
open scoped BigOperators
open UnityNativeWeights UnityNativeHilbert UnityNativeProjection UnityNativeCopies

@[simp] theorem clock_value_all (j m : ℕ) : value (clock j) m = clockValue j m := by
  by_cases hm : m=0
  · simp [hm, clockValue]
  · exact clock_value j (Nat.pos_of_ne_zero hm)

theorem clockValue_floor (j m : ℕ) :
    clockValue j m = (m : ℝ)/j - ((m/j : ℕ) : ℝ) := by
  simp only [clockValue, Int.fract, Int.floor_div_natCast, Int.floor_natCast]
  norm_cast

/-- Integer division acts on actual clocks by the exact two-clock formula. -/
theorem clockValue_copy (b j m : ℕ) (hb : 0<b) (hj : 0<j) :
    clockValue j (m/b) = clockValue (b*j) m - (j : ℝ)⁻¹ * clockValue b m := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  simp only [clockValue_floor, Nat.div_div_eq_div_mul, Nat.cast_mul]
  field_simp
  ring

/-- Title: `A copied clock is an exact two-clock combination`. -/
theorem copy_clock (b j : ℕ) (hb : 0<b) (hj : 0<j) :
    copy b hb (clock j) = clock (b*j) - (j : ℝ)⁻¹ • clock b := by
  apply ext_value
  intro m hm
  rw [copy_value, clock_value_all]
  have hv : value (clock (b*j) - (j : ℝ)⁻¹ • clock b) m =
      clockValue (b*j) m - (j : ℝ)⁻¹ * clockValue b m := by
    have hs (f g : NativeHilbert) : value (f-g) m=value f m-value g m := by
      simp [value, Nat.ne_of_gt hm, sub_div]
    rw [hs, value_smul, clock_value_all, clock_value_all]
  rw [hv]
  exact clockValue_copy b j m hb hj

/-- Title: `Copied clock spaces remain admissible`. -/
theorem copy_clockSpace {b N : ℕ} (hb : 2≤b) {f : NativeHilbert}
    (hf : f∈clockSpace N) : copy b (by omega) f ∈ clockSpace (b*N) := by
  have hle : clockSpace N ≤ (clockSpace (b*N)).comap (copyLinear b (by omega)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_Icc] at hj
    change copy b (by omega) (clock j) ∈ clockSpace (b*N)
    rw [copy_clock b j (by omega) (by omega)]
    apply (clockSpace (b*N)).sub_mem
    · exact clock_mem (by nlinarith) (Nat.mul_le_mul_left b hj.2)
    · apply (clockSpace (b*N)).smul_mem
      exact clock_mem hb (by nlinarith)
  exact hle hf

/-- The initial native block which a zero-extended copy leaves behind. -/
def boundary (b : ℕ) (hb : 0<b) : NativeHilbert := unity-copy b hb unity

theorem boundary_value (b : ℕ) (hb : 0<b) {m : ℕ} (hm : 0<m) :
    value (boundary b hb) m = if m<b then 1 else 0 := by
  have hsub (f g : NativeHilbert) : value (f-g) m=value f m-value g m := by
    simp [value, Nat.ne_of_gt hm, sub_div]
  rw [boundary, hsub, unity_value hm, copy_value]
  by_cases hmb : m<b
  · simp [hmb, Nat.div_eq_of_lt hmb]
  · rw [if_neg hmb, unity_value (Nat.div_pos (by omega) hb)]
    ring

theorem boundary_inner_copy (b : ℕ) (hb : 0<b) (f : NativeHilbert) :
    inner ℝ (boundary b hb) (copy b hb f) = 0 := by
  rw [inner_eq_weighted]
  have hz (n : ℕ) : weight (n+1) * value (boundary b hb) (n+1) *
      value (copy b hb f) (n+1) = 0 := by
    rw [boundary_value b hb (by omega), copy_value]
    by_cases hn : n+1<b
    · simp [hn, Nat.div_eq_of_lt hn]
    · simp [hn]
  simp_rw [hz, tsum_zero]

/-- Title: `Integer copies scale the signed unity reading`.

 Exact scaling of the signed unity reading; no absolute values are inserted. -/
theorem copy_mean (b : ℕ) (hb : 0<b) (f : NativeHilbert) :
    inner ℝ unity (copy b hb f) = inner ℝ unity f / b := by
  have he : unity=boundary b hb+copy b hb unity := by unfold boundary; abel
  nth_rw 1 [he]
  rw [inner_add_left, boundary_inner_copy, zero_add, copy_inner]

/-- Title: `Exact energy of the initial native block`. -/
theorem boundary_norm_sq (b : ℕ) (hb : 0<b) :
    ‖boundary b hb‖^2 = 1-(b : ℝ)⁻¹ := by
  rw [boundary, norm_sub_sq_real, copy_norm_sq, unity_norm_sq, copy_mean,
    real_inner_self_eq_norm_sq, unity_norm_sq]
  ring

/-- Title: `Unity splits into its boundary block and integer copy`.

 The native constant splits into its initial block and its integer copy. -/
theorem unity_boundary_copy (b : ℕ) (hb : 0<b) :
    unity=boundary b hb+copy b hb unity := by unfold boundary; abel

end NField.Alignment.UnityNativeDilation
