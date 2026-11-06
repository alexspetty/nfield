/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeDilation

/-! # Native isometric copies and the literal root detail -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityNativeIsometry
open scoped BigOperators
open UnityNativeWeights UnityNativeHilbert UnityNativeProjection UnityNativeCopies UnityNativeDilation

/-- The isometric normalization of the actual integer copy. -/
def scaledCopy (b : ℕ) (hb : 0<b) : NativeHilbert →ₗᵢ[ℝ] NativeHilbert where
  toFun f := Real.sqrt (b : ℝ) • copy b hb f
  map_add' f g := by rw [copy_add, smul_add]
  map_smul' c f := by
    simp only [copy_smul, RingHom.id_apply]
    exact smul_comm _ _ _
  norm_map' f := by
    have he : ‖Real.sqrt (b : ℝ) • copy b hb f‖^2 = ‖f‖^2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (Nat.cast_nonneg _), copy_norm_sq]
      have hb0 : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
      field_simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- Title: `Isometric copies retain the native addresses`. -/
@[simp] theorem scaledCopy_value (b : ℕ) (hb : 0<b) (f : NativeHilbert) (m : ℕ) :
    value (scaledCopy b hb f) m = Real.sqrt (b : ℝ)*value f (m/b) := by
  change value (Real.sqrt (b : ℝ) • copy b hb f) m=_
  rw [value_smul, copy_value]

/-- The paper's binary isometry. -/
def binaryCopy : NativeHilbert →ₗᵢ[ℝ] NativeHilbert := scaledCopy 2 (by omega)

/-- The root detail in weighted coordinates is `sqrt 2` at address one. -/
def rootDetail : NativeHilbert := lp.single 2 0 1

@[simp] theorem rootDetail_norm : ‖rootDetail‖=1 := by
  rw [rootDetail, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  norm_num

/-- Title: `The root detail has unit native energy`. -/
@[simp] theorem rootDetail_norm_sq : ‖rootDetail‖^2=1 := by rw [rootDetail_norm]; norm_num

/-- Title: `The native root detail is supported at the first address`.

 Literal native values of the prescribed root detail. -/
theorem rootDetail_value {m : ℕ} (hm : 0<m) :
    value rootDetail m = if m=1 then Real.sqrt 2 else 0 := by
  by_cases hm1 : m=1
  · subst m
    norm_num [rootDetail, value, weight, Real.sqrt_div]
  · have hm0 : m-1≠0 := by omega
    simp [rootDetail, value, hm.ne', lp.single_apply_ne, hm0, hm1]

/-- Conditioning removes the old native clock projection. -/
def conditioned (N : ℕ) (f : NativeHilbert) : NativeHilbert := f-projection N f

/-- Title: `Removing the old clock projection does not increase cost`. -/
theorem conditioned_norm_le (N : ℕ) (f : NativeHilbert) : ‖conditioned N f‖≤‖f‖ := by
  rw [conditioned, projection, ← Submodule.starProjection_orthogonal_val]
  exact (clockSpace N)ᗮ.norm_starProjection_apply_le f

theorem conditioned_orthogonal (N : ℕ) (f : NativeHilbert) :
    conditioned N f∈(clockSpace N)ᗮ := Submodule.sub_starProjection_mem_orthogonal f

theorem conditioned_mem {N M : ℕ} (hNM : N≤M) {f : NativeHilbert}
    (hf : f∈clockSpace M) : conditioned N f∈clockSpace M := by
  apply (clockSpace M).sub_mem hf
  exact clockSpace_mono hNM ((clockSpace N).starProjection_apply_mem f)

/-- Title: `Conditioning preserves the full signed residual reading`.

 A residual reads a conditioned probe with its full signed reading. -/
theorem residual_conditioned_reading (N : ℕ) (f : NativeHilbert) :
    inner ℝ (UnityNativeHilbert.residual N) (conditioned N f) =
      inner ℝ (UnityNativeHilbert.residual N) f := by
  rw [conditioned, projection, inner_sub_right,
    residual_inner_zero N ((clockSpace N).starProjection_apply_mem f), sub_zero]

theorem scaledCopy_one (f : NativeHilbert) : scaledCopy 1 (by omega) f=f := by
  apply ext_value
  intro m hm
  simp only [scaledCopy_value, Nat.cast_one, Real.sqrt_one, one_mul, Nat.div_one]

/-- Title: `Native isometric copies compose exactly`. -/
theorem scaledCopy_comp (a b : ℕ) (ha : 0<a) (hb : 0<b) (f : NativeHilbert) :
    scaledCopy a ha (scaledCopy b hb f)=scaledCopy (a*b) (Nat.mul_pos ha hb) f := by
  change Real.sqrt (a : ℝ) • copy a ha (Real.sqrt (b : ℝ) • copy b hb f)=
    Real.sqrt ((a*b : ℕ) : ℝ) • copy (a*b) (Nat.mul_pos ha hb) f
  rw [copy_smul, copy_copy, smul_smul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]

/-- Title: `Normalized integer copies remain admissible clocks`.

 The normalized copy remains an actual admitted clock vector. -/
theorem scaledCopy_clockSpace (b : ℕ) (hb : 0<b) (N : ℕ) {f : NativeHilbert}
    (hf : f∈clockSpace N) : scaledCopy b hb f∈clockSpace (b*N) := by
  by_cases hb2 : 2≤b
  · apply (clockSpace (b*N)).smul_mem
    exact copy_clockSpace hb2 hf
  · have hb1 : b=1 := by omega
    subst b
    simpa only [scaledCopy_one, one_mul] using hf

/-- Title: `Exact normalized clock lift at every integer scale`.

 Exact normalized clock lift at every integer copy scale. -/
theorem scaledCopy_clock (b j : ℕ) (hb : 0<b) (hj : 0<j) :
    scaledCopy b hb (clock j) =
      Real.sqrt (b : ℝ) • (clock (b*j)-(j : ℝ)⁻¹ • clock b) := by
  change Real.sqrt (b : ℝ) • copy b hb (clock j)=_
  rw [copy_clock b j hb hj]

/-- Title: `Iterated binary copying is the exact integer-scale isometry`.

 The binary isometry's iterates are the normalized complete integer copies. -/
theorem binary_iterate (h : ℕ) (f : NativeHilbert) :
    (binaryCopy^[h]) f=scaledCopy (2^h) (by positivity) f := by
  induction h with
  | zero => simpa using (scaledCopy_one f).symm
  | succ h ih =>
    rw [Function.iterate_succ_apply', ih]
    change scaledCopy 2 (by omega) (scaledCopy (2^h) (by positivity) f)=_
    rw [scaledCopy_comp]
    simp only [pow_succ']

end NField.Alignment.UnityNativeIsometry
