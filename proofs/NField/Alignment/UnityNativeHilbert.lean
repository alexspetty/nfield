/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeWeights

/-!
# The actual native weighted Hilbert space

The native sequence `f(m)` is represented in Mathlib's complete `ℓ²` by
`sqrt (1 / (m * (m + 1))) * f(m)`, for `m ≥ 1`. The inverse decoding below
is defined for every Hilbert vector and is extended by zero at the origin.
Thus all inner products retain the published reciprocal weights.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityNativeHilbert
open scoped BigOperators
open UnityNativeWeights

abbrev NativeHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Squared norm of the scaled coordinate used by the native model. -/
theorem scaled_square (n : ℕ) (a : ℝ) :
    ‖Real.sqrt (weight (n+1)) * a‖ ^ (2 : ℝ) = weight (n+1) * a^2 := by
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (weight_nonneg _)]

/-- A sequence is admitted with precisely its native weighted square sum. -/
def ofFunction (f : ℕ → ℝ)
    (hf : Summable (fun n : ℕ => weight (n+1) * f (n+1)^2)) : NativeHilbert :=
  ⟨fun n => Real.sqrt (weight (n+1)) * f (n+1),
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat, scaled_square] using hf)⟩

/-- Recover the unscaled sequence; zero is the fixed boundary convention. -/
def value (f : NativeHilbert) (m : ℕ) : ℝ :=
  if m = 0 then 0 else f (m-1) / Real.sqrt (weight m)

@[simp] theorem value_zero (f : NativeHilbert) : value f 0 = 0 := by simp [value]

@[simp] theorem value_succ (f : NativeHilbert) (n : ℕ) :
    value f (n+1) = f n / Real.sqrt (weight (n+1)) := by simp [value]

@[simp] theorem value_ofFunction (f : ℕ → ℝ)
    (hf : Summable (fun n : ℕ => weight (n+1) * f (n+1)^2))
    {m : ℕ} (hm : 0 < m) : value (ofFunction f hf) m = f m := by
  have hw : Real.sqrt (weight m) ≠ 0 := (Real.sqrt_pos.2 (weight_pos hm)).ne'
  simp [value, ofFunction, Nat.ne_of_gt hm, Nat.sub_add_cancel hm, hw]

@[simp] theorem coordinate_value (f : NativeHilbert) (n : ℕ) :
    Real.sqrt (weight (n+1)) * value f (n+1) = f n := by
  rw [value_succ]
  have hw : Real.sqrt (weight (n+1)) ≠ 0 :=
    (Real.sqrt_pos.2 (weight_pos (by omega))).ne'
  field_simp

/-- Evaluation is pointwise linear, including the fixed zero boundary. -/
theorem value_add (f g : NativeHilbert) (m : ℕ) :
    value (f+g) m = value f m + value g m := by
  by_cases hm : m=0
  · simp [hm]
  · simp [value, hm, lp.coeFn_add, add_div]

theorem value_smul (c : ℝ) (f : NativeHilbert) (m : ℕ) :
    value (c • f) m = c * value f m := by
  by_cases hm : m=0
  · simp [hm]
  · simp [value, hm, lp.coeFn_smul, mul_div_assoc]

/-- Equality of every positive native coordinate is equality in the Hilbert space. -/
theorem ext_value {f g : NativeHilbert}
    (h : ∀ m : ℕ, 0<m → value f m = value g m) : f=g := by
  apply lp.ext
  funext n
  rw [← coordinate_value f n, ← coordinate_value g n, h (n+1) (by omega)]

theorem weighted_inner_term (f g : NativeHilbert) (n : ℕ) :
    weight (n+1) * value f (n+1) * value g (n+1) = f n * g n := by
  rw [← Real.sq_sqrt (weight_nonneg (n+1))]
  calc
    Real.sqrt (weight (n+1)) ^ 2 * value f (n+1) * value g (n+1) =
      (Real.sqrt (weight (n+1)) * value f (n+1)) *
      (Real.sqrt (weight (n+1)) * value g (n+1)) := by ring
    _ = f n * g n := by rw [coordinate_value, coordinate_value]

theorem weighted_inner_summable (f g : NativeHilbert) :
    Summable (fun n : ℕ => weight (n+1) * value f (n+1) * value g (n+1)) := by
  simp_rw [weighted_inner_term]
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using (lp.summable_inner (𝕜 := ℝ) f g)

/-- Title: `The Hilbert inner product retains the native weights`.

 The Mathlib inner product is exactly the printed native inner product. -/
theorem inner_eq_weighted (f g : NativeHilbert) :
    inner ℝ f g = ∑' n : ℕ, weight (n+1) * value f (n+1) * value g (n+1) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [weighted_inner_term]
  simp [RCLike.inner_apply, mul_comm]

/-- Title: `Native squared norm is the weighted square sum`. -/
theorem norm_sq_eq_weighted (f : NativeHilbert) :
    ‖f‖^2 = ∑' n : ℕ, weight (n+1) * value f (n+1)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_weighted]
  apply tsum_congr
  intro n
  ring

theorem ofFunction_norm_sq (f : ℕ → ℝ)
    (hf : Summable (fun n : ℕ => weight (n+1) * f (n+1)^2)) :
    ‖ofFunction f hf‖^2 = ∑' n : ℕ, weight (n+1) * f (n+1)^2 := by
  rw [norm_sq_eq_weighted]
  apply tsum_congr
  intro n
  rw [value_ofFunction f hf (by omega)]

/-- Every bounded sequence belongs to the probability-weighted Hilbert space. -/
theorem bounded_summable (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ m : ℕ, 0<m → |f m| ≤ C) :
    Summable (fun n : ℕ => weight (n+1) * f (n+1)^2) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_nonneg _) (sq_nonneg _)) _
    (weights_summable.mul_right (C^2))
  intro n
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg _)
  have h := hf (n+1) (by omega)
  nlinarith [sq_abs (f (n+1)), abs_nonneg (f (n+1))]

/-- The constant unity sequence in the actual native Hilbert space. -/
def unity : NativeHilbert := ofFunction (fun _ => 1)
  (by simpa using weights_summable)

@[simp] theorem unity_value {m : ℕ} (hm : 0<m) : value unity m = 1 :=
  value_ofFunction _ _ hm

/-- Title: `Unity has unit native energy`. -/
@[simp] theorem unity_norm_sq : ‖unity‖^2 = 1 := by
  rw [unity, ofFunction_norm_sq]
  simpa using weights_tsum

@[simp] theorem unity_norm : ‖unity‖ = 1 := by
  have h := unity_norm_sq
  nlinarith [norm_nonneg unity]

/-- The published fractional clock, including its exact values at integer arguments. -/
def clockValue (j m : ℕ) : ℝ := Int.fract ((m : ℝ) / j)

theorem clockValue_nonneg (j m : ℕ) : 0 ≤ clockValue j m := Int.fract_nonneg _
theorem clockValue_lt_one (j m : ℕ) : clockValue j m < 1 := Int.fract_lt_one _

/-- An actual clock as a vector of the native weighted Hilbert space. -/
def clock (j : ℕ) : NativeHilbert := ofFunction (clockValue j)
  (bounded_summable _ 1 (fun m _ => by
    rw [abs_of_nonneg (clockValue_nonneg j m)]
    exact (clockValue_lt_one j m).le))

@[simp] theorem clock_value (j : ℕ) {m : ℕ} (hm : 0<m) :
    value (clock j) m = clockValue j m := value_ofFunction _ _ hm

/-- The actual finite clock subspace from the paper. -/
def clockSpace (N : ℕ) : Submodule ℝ NativeHilbert :=
  Submodule.span ℝ (clock '' (Finset.Icc 2 N : Set ℕ))

instance clockSpace_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (clockSpace N) :=
  FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet _).image clock)

theorem clock_mem {j N : ℕ} (hj : 2 ≤ j) (hjN : j ≤ N) : clock j ∈ clockSpace N := by
  apply Submodule.subset_span
  exact ⟨j, by simp [hj, hjN], rfl⟩

theorem clockSpace_mono : Monotone clockSpace := by
  intro N M h
  apply Submodule.span_mono
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_Icc] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

/-- Actual orthogonal projection onto the first finite clocks. -/
def projection (N : ℕ) : NativeHilbert →L[ℝ] NativeHilbert := (clockSpace N).starProjection

def fittedUnity (N : ℕ) : NativeHilbert := projection N unity
def residual (N : ℕ) : NativeHilbert := unity - fittedUnity N
def deficit (N : ℕ) : ℝ := ‖residual N‖^2

end NField.Alignment.UnityNativeHilbert
