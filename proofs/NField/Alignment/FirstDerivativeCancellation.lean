/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerKernel

/-! # Finite cancellation by inverse chords and total variation
These are the summation and variation steps of the first-derivative method.
Analytic monotonicity of phase increments remains a separate obligation.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FirstDerivativeCancellation
open scoped BigOperators Classical

def inverseChord (z : ℂ) : ℂ := (z-1)⁻¹

/-- The inverse chord of a unit complex number lies on a fixed vertical line. -/
theorem inverseChord_re (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    (inverseChord z).re = -1/2 := by
  have hn : z.re*z.re+z.im*z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hd : Complex.normSq (z-1) ≠ 0 := (Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)).ne'
  unfold inverseChord
  rw [Complex.inv_re]
  apply (div_eq_iff hd).mpr
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  nlinarith

theorem norm_of_zero_re (z : ℂ) (hz : z.re = 0) : ‖z‖ = |z.im| := by
  have he : z = (z.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hz]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  simp

/-- Exact finite summation by parts in endpoint form. -/
theorem weighted_increment_sum (a z : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), a i*(z (i+1)-z i)) =
      a N*z (N+1)-a 0*z 0 +
        ∑ i ∈ Finset.range N, (a i-a (i+1))*z (i+1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- On a vertical line, monotone imaginary parts give exact endpoint variation. -/
theorem vertical_variation (a : ℕ → ℂ) (hre : ∀ i, (a i).re = (a 0).re)
    (hmono : Monotone (fun i => (a i).im) ∨ Antitone (fun i => (a i).im)) (N : ℕ) :
    (∑ i ∈ Finset.range N, ‖a (i+1)-a i‖) = |(a N).im-(a 0).im| := by
  have he (i : ℕ) : ‖a (i+1)-a i‖ = |(a (i+1)).im-(a i).im| := by
    simpa only [Complex.sub_im] using norm_of_zero_re (a (i+1)-a i)
      (by simp only [Complex.sub_re, hre, sub_self])
  simp_rw [he]
  rcases hmono with hm | hm
  · have ht (i : ℕ) : 0 ≤ (a (i+1)).im-(a i).im := sub_nonneg.mpr (hm (Nat.le_succ i))
    simp_rw [abs_of_nonneg (ht _)]
    rw [Finset.sum_range_sub (fun i => (a i).im) N, abs_of_nonneg (sub_nonneg.mpr (hm (Nat.zero_le N)))]
  · have ht (i : ℕ) : (a (i+1)).im-(a i).im ≤ 0 := sub_nonpos.mpr (hm (Nat.le_succ i))
    simp_rw [abs_of_nonpos (ht _)]
    rw [Finset.sum_neg_distrib, Finset.sum_range_sub (fun i => (a i).im) N,
      abs_of_nonpos (sub_nonpos.mpr (hm (Nat.zero_le N)))]

/-- Cancellation of unit phases from inverse-chord endpoint norms and
monotone variation. Phase monotonicity must be established by the application. -/
theorem cancellation_from_inverse_chords (u z : ℕ → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (hu1 : ∀ i, u i ≠ 1)
    (hz : ∀ i, ‖z i‖ = 1) (hstep : ∀ i, z (i+1) = u i*z i)
    (hmono : Monotone (fun i => (inverseChord (u i)).im) ∨
      Antitone (fun i => (inverseChord (u i)).im)) (N : ℕ) :
    ‖∑ i ∈ Finset.range (N+1), z i‖ ≤
      2*(‖inverseChord (u N)‖+‖inverseChord (u 0)‖) := by
  let a := fun i => inverseChord (u i)
  have hre (i : ℕ) : (a i).re = (a 0).re := by
    dsimp [a]
    rw [inverseChord_re _ (hu i) (hu1 i), inverseChord_re _ (hu 0) (hu1 0)]
  have hi (i : ℕ) : a i*(z (i+1)-z i) = z i := by
    rw [hstep]
    dsimp [a, inverseChord]
    rw [← sub_one_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr (hu1 i))]
  have he := weighted_increment_sum a z N
  simp_rw [hi] at he
  have hv := vertical_variation a hre hmono N
  have hvar : (∑ i ∈ Finset.range N, ‖a i-a (i+1)‖) ≤ ‖a N‖+‖a 0‖ := by
    have heq : (∑ i ∈ Finset.range N, ‖a i-a (i+1)‖) =
        ∑ i ∈ Finset.range N, ‖a (i+1)-a i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact norm_sub_rev _ _
    rw [heq]
    rw [hv]
    calc
      _ ≤ |(a N).im|+|(a 0).im| := by simpa using abs_sub_le (a N).im 0 (a 0).im
      _ ≤ _ := add_le_add (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _)
  rw [he]
  calc
    _ ≤ ‖a N*z (N+1)-a 0*z 0‖+
        ‖∑ i ∈ Finset.range N, (a i-a (i+1))*z (i+1)‖ := norm_add_le _ _
    _ ≤ (‖a N‖+‖a 0‖)+(∑ i ∈ Finset.range N, ‖a i-a (i+1)‖) := by
      apply add_le_add
      · simpa only [norm_mul, hz, mul_one] using norm_sub_le (a N*z (N+1)) (a 0*z 0)
      · simpa only [norm_mul, hz, mul_one] using norm_sum_le (Finset.range N)
          (fun i => (a i-a (i+1))*z (i+1))
    _ ≤ _ := by dsimp [a] at *; linarith

end NField.Alignment.FirstDerivativeCancellation
