/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalFirstDerivativeBound

/-! # First differences of actual real reciprocal phases -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalDifferenceBound
open scoped BigOperators ComplexConjugate
open FirstDerivativeCancellation InverseChordMonotonicity
  ReciprocalFirstDerivativeBound ReciprocalWeightedBlocks

def differencePhase (p h : ℕ) (Q : ℝ) (i : ℕ) : ℂ :=
  fourier 1 ((Q/((p:ℝ)+i+h+1)-Q/((p:ℝ)+i+1) : ℝ) : AddCircle (1:ℝ))

def differenceIncrement (p h : ℕ) (Q : ℝ) (i : ℕ) : ℝ :=
  Q*(h:ℝ)/(((p:ℝ)+i+1)*((p:ℝ)+i+2)*((p:ℝ)+i+h+1)) +
    Q*(h:ℝ)/(((p:ℝ)+i+2)*((p:ℝ)+i+h+1)*((p:ℝ)+i+h+2))

theorem difference_step (p h i : ℕ) (Q : ℝ) :
    differencePhase p h Q (i+1) =
      fourier 1 (differenceIncrement p h Q i : AddCircle (1:ℝ))*
        differencePhase p h Q i := by
  unfold differencePhase
  rw [← character_add]
  unfold differenceIncrement
  congr 2
  push_cast
  field_simp
  ring

theorem difference_increment_pos (p h i : ℕ) (Q : ℝ)
    (hh : 1 ≤ h) (hQ : 0 < Q) : 0 < differenceIncrement p h Q i := by
  unfold differenceIncrement
  have hh0 : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  positivity

theorem difference_increment_antitone (p h : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    Antitone (differenceIncrement p h Q) := by
  intro i j hij
  unfold differenceIncrement
  apply add_le_add <;>
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) <;> gcongr

theorem difference_increment_upper (p h i : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hQ : 0 ≤ Q) :
    differenceIncrement p h Q i ≤ 2*Q*(h:ℝ)/(p:ℝ)^3 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hb₁ : Q*(h:ℝ)/(((p:ℝ)+i+1)*((p:ℝ)+i+2)*((p:ℝ)+i+h+1)) ≤
      Q*(h:ℝ)/(p:ℝ)^3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc
      (p:ℝ)^3 = (p:ℝ)*p*p := by ring
      _ ≤ _ := by gcongr <;> linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i), (Nat.cast_nonneg h : (0:ℝ) ≤ h)]
  have hb₂ : Q*(h:ℝ)/(((p:ℝ)+i+2)*((p:ℝ)+i+h+1)*((p:ℝ)+i+h+2)) ≤
      Q*(h:ℝ)/(p:ℝ)^3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc
      (p:ℝ)^3 = (p:ℝ)*p*p := by ring
      _ ≤ _ := by gcongr <;> linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i), (Nat.cast_nonneg h : (0:ℝ) ≤ h)]
  unfold differenceIncrement
  calc
    _ ≤ Q*(h:ℝ)/(p:ℝ)^3+Q*(h:ℝ)/(p:ℝ)^3 := add_le_add hb₁ hb₂
    _ = _ := by ring

theorem difference_increment_half (p h i : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hQ : 0 ≤ Q) (hsmall : 4*Q*(h:ℝ) ≤ (p:ℝ)^3) :
    differenceIncrement p h Q i ≤ 1/2 := by
  apply (difference_increment_upper p h i Q hp hQ).trans
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (p:ℝ)^3)).mpr
  linarith

theorem difference_increment_lower (p h i : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hh : h ≤ p) (hi : i < p) (hQ : 0 ≤ Q) :
    Q*(h:ℝ)/(64*(p:ℝ)^3) ≤ differenceIncrement p h Q i := by
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hhR : (h:ℝ) ≤ p := by exact_mod_cast hh
  have hiR : (i:ℝ)+1 ≤ p := by exact_mod_cast hi
  have hd : ((p:ℝ)+i+1)*((p:ℝ)+i+2)*((p:ℝ)+i+h+1) ≤ 64*(p:ℝ)^3 := by
    calc
      _ ≤ (4*(p:ℝ))*(4*(p:ℝ))*(4*(p:ℝ)) := by
        gcongr <;> linarith
      _ = _ := by ring
  unfold differenceIncrement
  have hb := div_le_div_of_nonneg_left (show 0 ≤ Q*(h:ℝ) by positivity)
    (show 0 < ((p:ℝ)+i+1)*((p:ℝ)+i+2)*((p:ℝ)+i+h+1) by positivity) hd
  exact hb.trans (le_add_of_nonneg_right (by positivity))

theorem difference_prefix_bound (p h M : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hh : 1 ≤ h) (hhp : h ≤ p) (hM : M ≤ p)
    (hQ : 0 < Q) (hsmall : 4*Q*(h:ℝ) ≤ (p:ℝ)^3) :
    ‖∑ i ∈ Finset.range M, differencePhase p h Q i‖ ≤
      64*(p:ℝ)^3/(Q*(h:ℝ)) := by
  have hh0 : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hu (i : ℕ) : ‖fourier 1 (differenceIncrement p h Q i : AddCircle (1:ℝ))‖ = 1 :=
    Circle.norm_coe _
  have hpos (i : ℕ) := difference_increment_pos p h i Q hh hQ
  have hhalf (i : ℕ) := difference_increment_half p h i Q hp hQ.le hsmall
  have hu1 (i : ℕ) : fourier 1 (differenceIncrement p h Q i : AddCircle (1:ℝ)) ≠ 1 :=
    character_ne_one _ (hpos i) (by linarith [hhalf i])
  have hmono : Antitone (fun i =>
      (inverseChord (fourier 1 (differenceIncrement p h Q i : AddCircle (1:ℝ)))).im) := by
    intro i j hij
    exact inverseChord_im_monotone _ _ (hpos j) (by linarith [hhalf i])
      (difference_increment_antitone p h Q hQ.le hij)
  have hend (i : ℕ) (hi : i < p) :
      ‖inverseChord (fourier 1 (differenceIncrement p h Q i : AddCircle (1:ℝ)))‖ ≤
        16*(p:ℝ)^3/(Q*(h:ℝ)) := by
    have hb := inverseChord_norm_bound _ (hpos i) (hhalf i)
    have hl := difference_increment_lower p h i Q hp hhp hi hQ.le
    apply hb.trans
    calc
      _ ≤ 1/(4*(Q*(h:ℝ)/(64*(p:ℝ)^3))) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        linarith
      _ = _ := by field_simp; ring
  cases M with
  | zero => simp; positivity
  | succ N =>
    have hb := cancellation_from_inverse_chords _ (differencePhase p h Q) hu hu1
      (fun i => Circle.norm_coe _) (fun i => difference_step p h i Q) (Or.inr hmono) N
    have h0 := hend 0 (by omega)
    have hN := hend N (by omega)
    calc
      _ ≤ 2*(‖inverseChord (fourier 1 (differenceIncrement p h Q N : AddCircle (1:ℝ)))‖+
          ‖inverseChord (fourier 1 (differenceIncrement p h Q 0 : AddCircle (1:ℝ)))‖) := hb
      _ ≤ 2*(16*(p:ℝ)^3/(Q*(h:ℝ))+16*(p:ℝ)^3/(Q*(h:ℝ))) := by gcongr
      _ = _ := by ring

end NField.Alignment.ReciprocalDifferenceBound
