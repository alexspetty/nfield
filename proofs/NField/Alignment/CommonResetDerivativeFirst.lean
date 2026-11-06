/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalFirstDerivativeBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv

/-! # First-derivative cancellation on the actual finite interval -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CommonResetDerivativeFirst

open scoped BigOperators ComplexConjugate
open FirstDerivativeCancellation InverseChordMonotonicity FejerKernel

def phase (x : ℝ) : ℂ := fourier 1 (x : AddCircle (1 : ℝ))

theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := Circle.norm_coe _

theorem phase_add (x y : ℝ) : phase (x+y) = phase x*phase y :=
  ReciprocalFirstDerivativeBound.character_add x y

theorem phase_int (k : ℤ) : phase (k : ℝ) = 1 := by
  unfold phase
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
  rw [hk]
  simp

theorem phase_sub_int (x : ℝ) (k : ℤ) : phase (x-(k : ℝ)) = phase x := by
  have hk : phase (-(k : ℝ)) = 1 := by simpa using phase_int (-k)
  rw [sub_eq_add_neg, phase_add, hk, mul_one]

theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase
  rw [AddCircle.coe_neg, fourier_apply, smul_neg, ← neg_smul, ← fourier_apply, fourier_neg]

theorem phase_exp (x : ℝ) : phase x = Complex.exp (Complex.ofReal (2*Real.pi*x)*Complex.I) :=
  character_exp x

theorem chord_reflection (x : ℝ) : ‖inverseChord (phase (1-x))‖ = ‖inverseChord (phase x)‖ := by
  unfold inverseChord phase
  rw [norm_inv, norm_inv, character_distance, character_distance]
  have he : Real.pi*(1-x) = Real.pi-Real.pi*x := by ring
  rw [he, Real.sin_pi_sub]

/-- Title: `The inverse chord is controlled by distance from either integer endpoint`. -/
theorem chord_bound_strip {x d : ℝ} (hd : 0 < d) (hlo : d ≤ x) (hhi : x ≤ 1-d) :
    ‖inverseChord (phase x)‖ ≤ 1/(4*d) := by
  by_cases hx : x ≤ 1/2
  · exact (inverseChord_norm_bound x (hd.trans_le hlo) hx).trans
      (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  · rw [← chord_reflection]
    exact (inverseChord_norm_bound (1-x) (by linarith) (by linarith)).trans
      (one_div_le_one_div_of_le (by positivity) (by nlinarith))

theorem vertical_variation_local (a : ℕ → ℂ) (N : ℕ)
    (hre : ∀ i ≤ N, (a i).re = (a 0).re)
    (hmono : (∀ i j, i ≤ j → j ≤ N → (a i).im ≤ (a j).im) ∨
      (∀ i j, i ≤ j → j ≤ N → (a j).im ≤ (a i).im)) :
    (∑ i ∈ Finset.range N, ‖a (i+1)-a i‖) = |(a N).im-(a 0).im| := by
  have he (i : ℕ) (hi : i < N) : ‖a (i+1)-a i‖ = |(a (i+1)).im-(a i).im| := by
    simpa only [Complex.sub_im] using norm_of_zero_re (a (i+1)-a i)
      (by rw [Complex.sub_re, hre (i+1) (by omega), hre i (by omega), sub_self])
  rw [Finset.sum_congr rfl (fun i hi => he i (Finset.mem_range.mp hi))]
  rcases hmono with hm|hm
  · have hpoint (i : ℕ) (hi : i ∈ Finset.range N) :
        |(a (i+1)).im-(a i).im| = (a (i+1)).im-(a i).im :=
      abs_of_nonneg (sub_nonneg.mpr (hm i (i+1) (by omega) (by have hh := Finset.mem_range.mp hi; omega)))
    rw [Finset.sum_congr rfl hpoint, Finset.sum_range_sub (fun i => (a i).im) N,
      abs_of_nonneg (sub_nonneg.mpr (hm 0 N (by omega) le_rfl))]
  · have hpoint (i : ℕ) (hi : i ∈ Finset.range N) :
        |(a (i+1)).im-(a i).im| = -((a (i+1)).im-(a i).im) :=
      abs_of_nonpos (sub_nonpos.mpr (hm i (i+1) (by omega) (by have hh := Finset.mem_range.mp hi; omega)))
    rw [Finset.sum_congr rfl hpoint, Finset.sum_neg_distrib, Finset.sum_range_sub (fun i => (a i).im) N,
      abs_of_nonpos (sub_nonpos.mpr (hm 0 N (by omega) le_rfl))]

theorem cancellation_local (u z : ℕ → ℂ) (N : ℕ)
    (hu : ∀ i ≤ N, ‖u i‖ = 1) (hu1 : ∀ i ≤ N, u i ≠ 1)
    (hz : ∀ i ≤ N+1, ‖z i‖ = 1) (hstep : ∀ i ≤ N, z (i+1) = u i*z i)
    (hmono : (∀ i j, i ≤ j → j ≤ N →
        (inverseChord (u i)).im ≤ (inverseChord (u j)).im) ∨
      (∀ i j, i ≤ j → j ≤ N →
        (inverseChord (u j)).im ≤ (inverseChord (u i)).im)) :
    ‖∑ i ∈ Finset.range (N+1), z i‖ ≤
      2*(‖inverseChord (u N)‖+‖inverseChord (u 0)‖) := by
  let a := fun i => inverseChord (u i)
  have hre (i : ℕ) (hi : i ≤ N) : (a i).re = (a 0).re := by
    dsimp [a]
    rw [inverseChord_re _ (hu i hi) (hu1 i hi),
      inverseChord_re _ (hu 0 (by omega)) (hu1 0 (by omega))]
  have hi (i : ℕ) (hi : i ≤ N) : a i*(z (i+1)-z i) = z i := by
    rw [hstep i hi]
    dsimp [a, inverseChord]
    rw [← sub_one_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr (hu1 i hi))]
  have he := weighted_increment_sum a z N
  rw [Finset.sum_congr rfl (fun i hi' => hi i (by have hh := Finset.mem_range.mp hi'; omega))] at he
  have hv := vertical_variation_local a N hre hmono
  have hvar : (∑ i ∈ Finset.range N, ‖a i-a (i+1)‖) ≤ ‖a N‖+‖a 0‖ := by
    rw [Finset.sum_congr rfl (fun i _ => norm_sub_rev (a i) (a (i+1))), hv]
    calc
      _ ≤ |(a N).im|+|(a 0).im| := by simpa using abs_sub_le (a N).im 0 (a 0).im
      _ ≤ _ := add_le_add (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _)
  have hend : ‖a N*z (N+1)-a 0*z 0‖ ≤ ‖a N‖+‖a 0‖ := by
    simpa only [norm_mul, hz (N+1) le_rfl, hz 0 (by omega), mul_one] using
      norm_sub_le (a N*z (N+1)) (a 0*z 0)
  have hsum : ‖∑ i ∈ Finset.range N, (a i-a (i+1))*z (i+1)‖ ≤
      ∑ i ∈ Finset.range N, ‖a i-a (i+1)‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi'
    rw [norm_mul, hz (i+1) (by have hh := Finset.mem_range.mp hi'; omega), mul_one]
  rw [he]
  have hn := norm_add_le (a N*z (N+1)-a 0*z 0)
    (∑ i ∈ Finset.range N, (a i-a (i+1))*z (i+1))
  dsimp [a] at *
  linarith

def increment (f : ℕ → ℝ) (i : ℕ) : ℝ := f (i+1)-f i

/-- Title: `Monotone increments away from integers give first-derivative cancellation`. -/
theorem discrete_first_derivative (f : ℕ → ℝ) (N : ℕ) (m : ℤ) (d : ℝ)
    (hd : 0 < d) (hdh : d ≤ 1/2)
    (hstrip : ∀ i < N, (m : ℝ)+d ≤ increment f i ∧ increment f i ≤ (m : ℝ)+1-d)
    (hmono : (∀ i j, i ≤ j → j < N → increment f i ≤ increment f j) ∨
      (∀ i j, i ≤ j → j < N → increment f j ≤ increment f i)) :
    ‖∑ i ∈ Finset.range (N+1), phase (f i)‖ ≤ 2/d := by
  cases N with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, phase_norm]
    exact (le_div_iff₀ hd).mpr (by linarith)
  | succ N =>
    let u : ℕ → ℂ := fun i => phase (increment f i-(m : ℝ))
    let z : ℕ → ℂ := fun i => phase (f i)
    have hu (i : ℕ) (_hi : i ≤ N) : ‖u i‖ = 1 := phase_norm _
    have hu1 (i : ℕ) (hi : i ≤ N) : u i ≠ 1 := by
      apply character_ne_one
      · linarith [(hstrip i (by omega)).1]
      · linarith [(hstrip i (by omega)).2]
    have hz (i : ℕ) (_hi : i ≤ N+1) : ‖z i‖ = 1 := phase_norm _
    have hstep (i : ℕ) (_hi : i ≤ N) : z (i+1) = u i*z i := by
      dsimp [u, z]
      rw [phase_sub_int, ← phase_add]
      congr 1
      simp [increment]
    have hchord : (∀ i j, i ≤ j → j ≤ N → (inverseChord (u i)).im ≤ (inverseChord (u j)).im) ∨
        (∀ i j, i ≤ j → j ≤ N → (inverseChord (u j)).im ≤ (inverseChord (u i)).im) := by
      rcases hmono with hm|hm
      · left
        intro i j hij hj
        apply inverseChord_im_monotone
        · linarith [(hstrip i (by omega)).1]
        · linarith [(hstrip j (by omega)).2]
        · exact sub_le_sub_right (hm i j hij (by omega)) _
      · right
        intro i j hij hj
        apply inverseChord_im_monotone
        · linarith [(hstrip j (by omega)).1]
        · linarith [(hstrip i (by omega)).2]
        · exact sub_le_sub_right (hm i j hij (by omega)) _
    have hcancel := cancellation_local u z N hu hu1 hz hstep hchord
    have hbound (i : ℕ) (hi : i ≤ N) : ‖inverseChord (u i)‖ ≤ 1/(4*d) := by
      apply chord_bound_strip hd
      · linarith [(hstrip i (by omega)).1]
      · linarith [(hstrip i (by omega)).2]
    have hs : ‖∑ i ∈ Finset.range (N+1), phase (f i)‖ ≤ 1/d := by
      have hN := hbound N le_rfl
      have h0 := hbound 0 (by omega)
      change ‖∑ i ∈ Finset.range (N+1), phase (f i)‖ ≤
        2*(‖inverseChord (u N)‖+‖inverseChord (u 0)‖) at hcancel
      calc
        _ ≤ 2*(1/(4*d)+1/(4*d)) := by linarith
        _ = _ := by ring
    rw [show N.succ+1=N+1+1 by omega, Finset.sum_range_succ]
    calc
      _ ≤ ‖∑ i ∈ Finset.range (N+1), phase (f i)‖+‖phase (f (N+1))‖ := norm_add_le _ _
      _ ≤ 1/d+1 := by rw [phase_norm]; linarith
      _ ≤ 2/d := by
        apply (le_div_iff₀ hd).mpr
        field_simp
        linarith

end NField.Alignment.CommonResetDerivativeFirst
