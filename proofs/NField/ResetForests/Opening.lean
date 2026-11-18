/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SignedRates
import NField.ResetForests.PhaseFringe
/-! # The controlled-forest theorem and its exact remaining target

The original sampling defect is retained. The selected signed forest is
bounded at first-power scale; both implications for the actual complement
then follow from its exact remainder, without assuming a half-power bound.
-/

noncomputable section

namespace NField.ResetForests.SignedForestWork

open NField.Alignment
open CommonResetSampling PhasePopulations

def otherForestReading (p D : ℕ) : ℝ :=
  Core.selectedReading (p-1) (p^2) (fun k => !(Core.forestMask (p-1) D k))

def centeredSamplingDefect (p : ℕ) : ℝ := defect (p-1) (p^2)-1

def forestRemainder (p D : ℕ) : ℝ :=
  centeredSamplingDefect p-4*otherForestReading p D/(p : ℝ)^2

theorem five_prime_defect : defect 4 25 = (143/225 : ℝ) := by
  rw [defect, Core.four_clock_continuous, Core.four_clock_sampled]
  norm_num

theorem forest_remainder_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (D : ℕ) :
    forestRemainder p D =
      4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2+
        (-2/(p : ℝ)+1/(p : ℝ)^2-
          ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)) := by
  have h := Core.prime_square_forest_decomposition hp hodd (Core.forestMask (p-1) D)
  unfold forestRemainder centeredSamplingDefect otherForestReading
  linear_combination h

theorem polynomial_forest_remainder (K C₀ ε : ℝ) (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → p ≠ 2 → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |forestRemainder p D| ≤ C*(p : ℝ)^(-1+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_signed_and_restoration_any_exponent K C₀ ε hC₀ hε
  refine ⟨4*C+4, by positivity, ?_⟩
  intro p D hp hodd hD hheight
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hinv : 1/(p : ℝ) ≤ (p : ℝ)^(-1+ε) := by
    calc
      _ = (p : ℝ)^(-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)
  rw [forest_remainder_identity hp hodd]
  calc
    _ ≤ |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2|+
        |-2/(p : ℝ)+1/(p : ℝ)^2-
          ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)| := abs_add_le _ _
    _ ≤ (4*|Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)|/(p : ℝ)^2)+4/(p : ℝ) := by
      apply add_le_add _ (smooth_correction_bound hp.one_le)
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
      norm_num
    _ ≤ (4*(C*(p : ℝ)^(1+ε))/(p : ℝ)^2)+4/(p : ℝ) := by
      exact add_le_add
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hc p D hp hD hheight).1 (by norm_num)) (sq_nonneg _)) (le_refl _)
    _ = (4*C)*(p : ℝ)^(-1+ε)+4/(p : ℝ) := by
      rw [show 4*(C*(p : ℝ)^(1+ε))/(p : ℝ)^2=(4*C)*((p : ℝ)^(1+ε)/(p : ℝ)^2) by ring,
        ← Real.rpow_two, ← Real.rpow_sub hpR, show (1+ε : ℝ)-2=-1+ε by ring]
    _ ≤ (4*C)*(p : ℝ)^(-1+ε)+4*(p : ℝ)^(-1+ε) := by
      apply add_le_add (le_refl _)
      calc
        4/(p : ℝ)=4*(1/(p : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

/-- A quantified uniform power bound along the original odd-prime cutoffs. -/
def PrimePowerRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ,
    p.Prime → p ≠ 2 → |f p| ≤ C*(p : ℝ)^(a+ε)

theorem scaled_half_rate_iff (f g : ℕ → ℝ)
    (hr : PrimePowerRate (fun p => f p-4*g p/(p : ℝ)^2) (-1)) :
    PrimePowerRate f (-1/2) ↔ PrimePowerRate g (3/2) := by
  constructor
  · intro hf ε hε
    obtain ⟨F, hF, hf⟩ := hf ε hε
    obtain ⟨R, hR, hr⟩ := hr ε hε
    refine ⟨(F+R)/4, by positivity, ?_⟩
    intro p hp hodd
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hrr : |f p-4*g p/(p : ℝ)^2| ≤ R*(p : ℝ)^(-1/2+ε) :=
      (hr p hp hodd).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) hR.le)
    have htri : |4*g p/(p : ℝ)^2| ≤ (F+R)*(p : ℝ)^(-1/2+ε) := by
      calc
        _ = |f p-(f p-4*g p/(p : ℝ)^2)| := by congr 1; ring
        _ ≤ |f p|+|f p-4*g p/(p : ℝ)^2| := by
          calc
            _ = |f p+ -(f p-4*g p/(p : ℝ)^2)| := rfl
            _ ≤ |f p|+|-(f p-4*g p/(p : ℝ)^2)| := abs_add_le _ _
            _ = _ := by rw [abs_neg]
        _ ≤ F*(p : ℝ)^(-1/2+ε)+R*(p : ℝ)^(-1/2+ε) := add_le_add (hf p hp hodd) hrr
        _ = _ := by ring
    calc
      |g p| = ((p : ℝ)^2/4)*|4*g p/(p : ℝ)^2| := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
        norm_num
        field_simp
      _ ≤ ((p : ℝ)^2/4)*((F+R)*(p : ℝ)^(-1/2+ε)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
      _ = ((F+R)/4)*((p : ℝ)^2*(p : ℝ)^(-1/2+ε)) := by ring
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_add hpR, show (2 : ℝ)+(-1/2+ε)=3/2+ε by ring]
  · intro hg ε hε
    obtain ⟨G, hG, hg⟩ := hg ε hε
    obtain ⟨R, hR, hr⟩ := hr ε hε
    refine ⟨4*G+R, by positivity, ?_⟩
    intro p hp hodd
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hrr : |f p-4*g p/(p : ℝ)^2| ≤ R*(p : ℝ)^(-1/2+ε) :=
      (hr p hp hodd).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) hR.le)
    have hg' : |4*g p/(p : ℝ)^2| ≤ (4*G)*(p : ℝ)^(-1/2+ε) := by
      calc
        _ = 4*|g p|/(p : ℝ)^2 := by
          rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
          norm_num
        _ ≤ 4*(G*(p : ℝ)^(3/2+ε))/(p : ℝ)^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hg p hp hodd) (by norm_num)) (sq_nonneg _)
        _ = _ := by
          rw [show 4*(G*(p : ℝ)^(3/2+ε))/(p : ℝ)^2=(4*G)*((p : ℝ)^(3/2+ε)/(p : ℝ)^2) by ring,
            ← Real.rpow_two, ← Real.rpow_sub hpR, show (3/2+ε : ℝ)-2=-1/2+ε by ring]
    calc
      _ = |4*g p/(p : ℝ)^2+(f p-4*g p/(p : ℝ)^2)| := by congr 1; ring
      _ ≤ |4*g p/(p : ℝ)^2|+|f p-4*g p/(p : ℝ)^2| := abs_add_le _ _
      _ ≤ (4*G)*(p : ℝ)^(-1/2+ε)+R*(p : ℝ)^(-1/2+ε) := add_le_add hg' hrr
      _ = _ := by ring

theorem polynomial_forest_half_rate_iff (K C₀ : ℝ) (hC₀ : 0 < C₀)
    (D : ℕ → ℕ)
    (hD : ∀ p : ℕ, p.Prime → p ≠ 2 → 1 ≤ D p ∧ (D p : ℝ) ≤ C₀*(p : ℝ)^K) :
    PrimePowerRate centeredSamplingDefect (-1/2) ↔
      PrimePowerRate (fun p => otherForestReading p (D p)) (3/2) := by
  apply scaled_half_rate_iff
  intro ε hε
  obtain ⟨C, hC, hc⟩ := polynomial_forest_remainder K C₀ ε hC₀ hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  exact hc p (D p) hp hodd (hD p hp hodd).1 (hD p hp hodd).2

end NField.ResetForests.SignedForestWork
