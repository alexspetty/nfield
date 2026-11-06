/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.InverseChordMonotonicity
import NField.Alignment.ReciprocalWeightedBlocks

/-! # Unconditional large-block real reciprocal cancellation -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalFirstDerivativeBound
open FirstDerivativeCancellation InverseChordMonotonicity ReciprocalWeightedBlocks
open scoped BigOperators Classical ComplexConjugate

def increment (p : ℕ) (Q : ℝ) (i : ℕ) : ℝ :=
  Q/(((p : ℝ)+i+1)*((p : ℝ)+i+2))

def negativePhase (p : ℕ) (Q : ℝ) (i : ℕ) : ℂ :=
  fourier 1 ((-Q/((p : ℝ)+i+1) : ℝ) : AddCircle (1 : ℝ))

theorem increment_positive (p i : ℕ) (Q : ℝ) (hQ : 0 < Q) : 0 < increment p Q i := by
  unfold increment
  positivity

theorem increment_half (p i : ℕ) (Q : ℝ) (hlarge : 2*Q ≤ (p : ℝ)^2) :
    increment p Q i ≤ 1/2 := by
  unfold increment
  apply (div_le_iff₀ (by positivity : 0 < ((p : ℝ)+i+1)*((p : ℝ)+i+2))).mpr
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hm : 0 ≤ (p : ℝ)*(i : ℝ) := by positivity
  nlinarith [sq_nonneg (i : ℝ)]

theorem increment_antitone (p : ℕ) (Q : ℝ) (hQ : 0 < Q) : Antitone (increment p Q) := by
  intro i j hij
  unfold increment
  apply div_le_div_of_nonneg_left hQ.le (by positivity)
  gcongr

theorem character_add (s t : ℝ) :
    fourier 1 ((s+t : ℝ) : AddCircle (1 : ℝ)) =
      fourier 1 (s : AddCircle (1 : ℝ))*fourier 1 (t : AddCircle (1 : ℝ)) := by
  simp only [AddCircle.coe_add, fourier_apply, one_zsmul, AddCircle.toCircle_add, Circle.coe_mul]

theorem reciprocal_step (p i : ℕ) (Q : ℝ) :
    negativePhase p Q (i+1) = fourier 1 (increment p Q i : AddCircle (1 : ℝ))*negativePhase p Q i := by
  unfold negativePhase
  rw [← character_add]
  unfold increment
  congr 2
  push_cast
  field_simp
  ring

theorem negative_prefix_norm (p M : ℕ) (Q : ℝ) :
    ‖∑ i ∈ Finset.range M, negativePhase p Q i‖ = ‖reciprocalPrefix p M Q‖ := by
  have hn (t : ℝ) : fourier 1 ((-t : ℝ) : AddCircle (1 : ℝ)) =
      conj (fourier 1 (t : AddCircle (1 : ℝ))) := by
    rw [AddCircle.coe_neg, fourier_apply, smul_neg, ← neg_smul, ← fourier_apply, fourier_neg]
  have he (i : ℕ) : negativePhase p Q i = conj (reciprocalPhase Q (p+i+1)) := by
    unfold negativePhase reciprocalPhase
    simp only [Nat.cast_add, Nat.cast_one, neg_div]
    exact hn _
  simp_rw [he]
  rw [← map_sum, Complex.norm_conj]
  rfl

/-- The actual inverse chords are monotone for the large-block range. -/
theorem reciprocal_chord_antitone (p : ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hlarge : 2*Q ≤ (p : ℝ)^2) :
    Antitone (fun i => (inverseChord (fourier 1 (increment p Q i : AddCircle (1 : ℝ)))).im) := by
  intro i j hij
  exact inverseChord_im_monotone _ _ (increment_positive p j Q hQ)
    (by linarith [increment_half p i Q hlarge]) (increment_antitone p Q hQ hij)

theorem reciprocal_chord_endpoint (p i : ℕ) (hp : 1 ≤ p) (hi : i < p)
    (Q : ℝ) (hQ : 0 < Q) (hlarge : 2*Q ≤ (p : ℝ)^2) :
    ‖inverseChord (fourier 1 (increment p Q i : AddCircle (1 : ℝ)))‖ ≤ 2*(p : ℝ)^2/Q := by
  have hb := inverseChord_norm_bound _ (increment_positive p i Q hQ) (increment_half p i Q hlarge)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hiR : (i : ℝ)+1 ≤ p := by exact_mod_cast hi
  have hd : ((p : ℝ)+i+1)*((p : ℝ)+i+2) ≤ (2*(p : ℝ))*(3*(p : ℝ)) := by
    apply mul_le_mul <;> first | positivity | nlinarith
  apply hb.trans
  calc
    _ = (((p : ℝ)+i+1)*((p : ℝ)+i+2))/(4*Q) := by unfold increment; field_simp
    _ ≤ (8*(p : ℝ)^2)/(4*Q) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by ring

/-- Unconditional first-derivative cancellation for every endpoint of a large block. -/
theorem large_block_prefix (p M : ℕ) (hp : 1 ≤ p) (hM : M ≤ p)
    (Q : ℝ) (hQ : 0 < Q) (hlarge : 2*Q ≤ (p : ℝ)^2) :
    ‖reciprocalPrefix p M Q‖ ≤ 8*(p : ℝ)^2/Q := by
  cases M with
  | zero => simp [reciprocalPrefix]; positivity
  | succ N =>
      rw [← negative_prefix_norm]
      have hu (i : ℕ) : ‖fourier 1 (increment p Q i : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
      have hu1 (i : ℕ) := character_ne_one _ (increment_positive p i Q hQ)
        (show increment p Q i < 1 by linarith [increment_half p i Q hlarge])
      have hz (i : ℕ) : ‖negativePhase p Q i‖ = 1 := Circle.norm_coe _
      have hb := cancellation_from_inverse_chords _ (negativePhase p Q) hu hu1 hz
        (fun i => reciprocal_step p i Q) (Or.inr (reciprocal_chord_antitone p Q hQ hlarge)) N
      have h0 := reciprocal_chord_endpoint p 0 hp (by omega) Q hQ hlarge
      have hN := reciprocal_chord_endpoint p N hp (by omega) Q hQ hlarge
      calc
        _ ≤ 2*(‖inverseChord (fourier 1 (increment p Q N : AddCircle (1 : ℝ)))‖+
          ‖inverseChord (fourier 1 (increment p Q 0 : AddCircle (1 : ℝ)))‖) := hb
        _ ≤ 2*(2*(p : ℝ)^2/Q+2*(p : ℝ)^2/Q) := by gcongr
        _ = _ := by ring

/-- The bounded parameter range is controlled by the exact number of terms. -/
theorem bounded_parameter_prefix (p M : ℕ) (hp : 1 ≤ p) (hM : M ≤ p)
    (Q : ℝ) (hQ : 0 < Q) (hQ512 : Q ≤ 512) :
    ‖reciprocalPrefix p M Q‖ ≤ 512*(p : ℝ)^2/Q := by
  have hn : ‖reciprocalPrefix p M Q‖ ≤ (M : ℝ) := by
    unfold reciprocalPrefix
    calc
      _ ≤ ∑ i ∈ Finset.range M, ‖reciprocalPhase Q (p+i+1)‖ := norm_sum_le _ _
      _ = M := by simp only [reciprocalPhase, fourier_apply, Circle.norm_coe,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hMr : (M : ℝ) ≤ p := by exact_mod_cast hM
  apply (hn.trans hMr).trans
  apply (le_div_iff₀ hQ).mpr
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := mul_le_mul_of_nonneg_left hQ512 (show (0 : ℝ) ≤ p by positivity)
  nlinarith

end NField.Alignment.ReciprocalFirstDerivativeBound
