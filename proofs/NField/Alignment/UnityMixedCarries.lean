/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeHilbert

/-! # Exact mixed-base ceiling carries and reconstruction -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityMixedCarries
open scoped BigOperators
open UnityNativeHilbert

/-- The literal product of the first mixed integer factors. -/
def scale (b : ℕ → ℕ) (t : ℕ) : ℕ := ∏ i ∈ Finset.range t, b i

@[simp] theorem scale_zero (b : ℕ → ℕ) : scale b 0=1 := by simp [scale]

theorem scale_succ (b : ℕ → ℕ) (t : ℕ) : scale b (t+1)=scale b t*b t := by
  simp only [scale, Finset.prod_range_succ]

theorem scale_pos (b : ℕ → ℕ) (hb : ∀t, 0<b t) (t : ℕ) : 0<scale b t := by
  unfold scale
  exact Finset.prod_pos (fun i _ => hb i)

/-- The exact ceiling error, including zero at integer arguments. -/
def ceilingError (x : ℝ) : ℝ := (⌈x⌉ : ℝ)-x

theorem ceilingError_nonneg (x : ℝ) : 0≤ceilingError x := by
  exact sub_nonneg.mpr (Int.le_ceil x)

theorem ceilingError_lt_one (x : ℝ) : ceilingError x<1 := by
  have h := Int.ceil_lt_add_one x
  unfold ceilingError
  linarith

/-- One mixed-base carry, as an actual integer. -/
def ceilingCarry (b : ℕ) (x : ℝ) : ℤ := (b : ℤ)*⌈x⌉-⌈(b : ℝ)*x⌉

theorem ceilingCarry_nonneg (b : ℕ) (x : ℝ) : 0≤ceilingCarry b x := by
  unfold ceilingCarry
  apply sub_nonneg.mpr
  apply Int.ceil_le.mpr
  push_cast
  exact mul_le_mul_of_nonneg_left (Int.le_ceil x) (Nat.cast_nonneg b)

theorem ceilingCarry_error (b : ℕ) (x : ℝ) :
    (ceilingCarry b x : ℝ) = (b : ℝ)*ceilingError x-ceilingError ((b : ℝ)*x) := by
  unfold ceilingCarry ceilingError
  push_cast
  ring

theorem ceilingCarry_lt {b : ℕ} (hb : 0<b) (x : ℝ) : ceilingCarry b x < (b : ℤ) := by
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have h := mul_lt_mul_of_pos_left (ceilingError_lt_one x) hbR
  have h0 := ceilingError_nonneg ((b : ℝ)*x)
  rw [mul_one] at h
  have hc := ceilingCarry_error b x
  have hh : (ceilingCarry b x : ℝ)<(b : ℝ) := by linarith
  exact_mod_cast hh

def rowError (b : ℕ → ℕ) (x : ℝ) (t : ℕ) : ℝ := ceilingError ((scale b t : ℝ)*x)
def rowCarry (b : ℕ → ℕ) (x : ℝ) (t : ℕ) : ℤ := ceilingCarry (b t) ((scale b t : ℝ)*x)

theorem rowCarry_formula (b : ℕ → ℕ) (x : ℝ) (t : ℕ) :
    rowCarry b x t = (b t : ℤ)*⌈(scale b t : ℝ)*x⌉-⌈(scale b (t+1) : ℝ)*x⌉ := by
  unfold rowCarry ceilingCarry
  rw [scale_succ, Nat.cast_mul]
  congr 2
  ring

/-- Title: `Every mixed carry stays in its base range`. -/
theorem rowCarry_range (b : ℕ → ℕ) (hb : ∀t, 2≤b t) (x : ℝ) (t : ℕ) :
    0≤rowCarry b x t ∧ rowCarry b x t<(b t : ℤ) :=
  ⟨ceilingCarry_nonneg _ _, ceilingCarry_lt (by have := hb t; omega) _⟩

theorem rowCarry_error (b : ℕ → ℕ) (x : ℝ) (t : ℕ) :
    (rowCarry b x t : ℝ) = (b t : ℝ)*rowError b x t-rowError b x (t+1) := by
  rw [rowCarry, ceilingCarry_error]
  unfold rowError
  rw [scale_succ, Nat.cast_mul]
  congr 2
  ring

/-- Title: `Mixed carries reconstruct the exact ceiling error`.

 Exact telescope of the actual carries for every finite depth, including zero. -/
theorem mixed_carry_reconstruction (b : ℕ → ℕ) (hb : ∀t, 2≤b t) (x : ℝ) (T : ℕ) :
    ceilingError x = (∑ t ∈ Finset.range T,
      (rowCarry b x t : ℝ)/(scale b (t+1) : ℝ)) + rowError b x T/(scale b T : ℝ) := by
  have hp (t : ℕ) : (scale b t : ℝ) ≠ 0 := by
    exact_mod_cast (scale_pos b (fun i => by have := hb i; omega) t).ne'
  have hbp (t : ℕ) : (b t : ℝ) ≠ 0 := by exact_mod_cast (by have := hb t; omega : b t≠0)
  have he (t : ℕ) : (rowCarry b x t : ℝ)/(scale b (t+1) : ℝ) =
      rowError b x t/(scale b t : ℝ)-rowError b x (t+1)/(scale b (t+1) : ℝ) := by
    rw [rowCarry_error, scale_succ, Nat.cast_mul]
    field_simp [hp t, hbp t]
  rw [Finset.sum_congr rfl (fun t _ => he t), Finset.sum_range_sub']
  simp [rowError]

/-- Literal terminal error bound for every mixed refinement. -/
theorem terminal_error_range (b : ℕ → ℕ) (hb : ∀t, 2≤b t) (x : ℝ) (T : ℕ) :
    0≤rowError b x T/(scale b T : ℝ) ∧
      rowError b x T/(scale b T : ℝ)<1/(scale b T : ℝ) := by
  have hp : (0 : ℝ)<scale b T := by
    exact_mod_cast scale_pos b (fun i => by have := hb i; omega) T
  exact ⟨div_nonneg (ceilingError_nonneg _) hp.le,
    (div_lt_div_iff_of_pos_right hp).mpr (ceilingError_lt_one _)⟩

/-- The ceiling error and fractional clock differ by the exact divisibility endpoint. -/
theorem clock_ceiling_relation (j n : ℕ) (hj : 0<j) :
    ceilingError ((n : ℝ)/j) = 1-(if j∣n then 1 else 0)-clockValue j n := by
  by_cases hjn : j∣n
  · obtain ⟨k, hk⟩ := hjn
    have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
    simp [ceilingError, clockValue, hk, mul_div_cancel_left₀, hj0]
  · have hfract : Int.fract ((n : ℝ)/j) ≠ 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      apply div_ne_zero
      · exact_mod_cast (fun he : n%j=0 => hjn (Nat.dvd_of_mod_eq_zero he))
      · exact_mod_cast hj.ne'
    have h := (Int.fract_eq_zero_or_add_one_sub_ceil ((n : ℝ)/j)).resolve_left hfract
    simp only [if_neg hjn, sub_zero]
    unfold ceilingError clockValue
    linarith

/-- The paper's resolved mixed-carry row. -/
def resolvedClock (b : ℕ → ℕ) (j T n : ℕ) : ℝ :=
  1-(if j∣n then 1 else 0)-
    ∑ t ∈ Finset.range T, (rowCarry b ((n : ℝ)/j) t : ℝ)/(scale b (t+1) : ℝ)

/-- Title: `Resolved clock error is the exact terminal carry remainder`. -/
theorem resolved_clock_error (b : ℕ → ℕ) (hb : ∀t, 2≤b t) (j T n : ℕ) (hj : 0<j) :
    resolvedClock b j T n-clockValue j n = rowError b ((n : ℝ)/j) T/(scale b T : ℝ) := by
  have h := mixed_carry_reconstruction b hb ((n : ℝ)/j) T
  rw [clock_ceiling_relation j n hj] at h
  unfold resolvedClock
  linarith

/-- Title: `Uniform endpoint bound for mixed-carry reconstruction`. -/
theorem resolved_clock_error_range (b : ℕ → ℕ) (hb : ∀t, 2≤b t)
    (j T n : ℕ) (hj : 0<j) :
    0≤resolvedClock b j T n-clockValue j n ∧
      resolvedClock b j T n-clockValue j n<1/(scale b T : ℝ) := by
  rw [resolved_clock_error b hb j T n hj]
  exact terminal_error_range b hb _ T

end NField.Alignment.UnityMixedCarries
