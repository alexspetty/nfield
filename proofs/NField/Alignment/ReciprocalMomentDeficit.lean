/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalParameterChoice

/-! # The concrete moment order absorbs the Vinogradov deficit -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalMomentDeficit
open ReciprocalParameterChoice

def deficit (m : ℕ) : ℝ :=
  (degree m:ℝ)^2*Real.exp 2*Real.exp (-(momentOrder m:ℝ)/(degree m:ℝ)^2)

theorem deficit_nonneg (m : ℕ) : 0 ≤ deficit m := by unfold deficit; positivity

theorem exp_neg_twenty_two : Real.exp (-22) ≤ (1:ℝ)/4194304 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 22
  have he : (4194304:ℝ) ≤ Real.exp 22 := by
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    exact hp
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he

theorem deficit_le (m : ℕ) (hm : 1 ≤ m) : deficit m ≤ (m:ℝ)^2/1024 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hd0 : (degree m:ℝ) ≠ 0 := by dsimp [degree]; positivity
  have hr : -(momentOrder m:ℝ)/(degree m:ℝ)^2 = -24 := by
    dsimp [momentOrder]
    push_cast
    field_simp
  unfold deficit
  rw [hr,mul_assoc,← Real.exp_add]
  norm_num only [show (2:ℝ)+(-24) = -22 by norm_num]
  have h := mul_le_mul_of_nonneg_left exp_neg_twenty_two (sq_nonneg (degree m:ℝ))
  dsimp [degree] at h ⊢
  push_cast at h ⊢
  nlinarith

theorem deficit_absorption (m : ℕ) (hm : 1 ≤ m) (L U : ℝ) (hL : 0 ≤ L)
    (hU : U ≤ L/2) :
    4*deficit m*U-(m:ℝ)^2*L/128 ≤ -(m:ℝ)^2*L/256 := by
  have h₁ := mul_le_mul_of_nonneg_left hU
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (deficit_nonneg m))
  have h₂ := mul_le_mul_of_nonneg_right (deficit_le m hm) hL
  have h₃ := mul_nonneg (sq_nonneg (m:ℝ)) hL
  nlinarith

def decayConstant : ℝ := 1/(2048*(24*64^2)^2)

theorem decayConstant_pos : 0 < decayConstant := by norm_num [decayConstant]

theorem decayConstant_le : decayConstant ≤ 1/32 := by norm_num [decayConstant]

theorem deficit_exponent_bound (m : ℕ) (hm : 1 ≤ m) (L U : ℝ) (hL : 0 ≤ L)
    (hU : U ≤ L/2) :
    (4*deficit m*U-(m:ℝ)^2*L/128)/(8*(momentOrder m:ℝ)^2) ≤
      -decayConstant*L/(m:ℝ)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hden : 0 ≤ 8*(momentOrder m:ℝ)^2 := by positivity
  calc
    _ ≤ (-(m:ℝ)^2*L/256)/(8*(momentOrder m:ℝ)^2) :=
      div_le_div_of_nonneg_right (deficit_absorption m hm L U hL hU) hden
    _ = _ := by
      dsimp [momentOrder,degree,decayConstant]
      push_cast
      field_simp
      ring

end NField.Alignment.ReciprocalMomentDeficit
