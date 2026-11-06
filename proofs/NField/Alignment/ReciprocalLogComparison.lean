/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalMomentDeficit

/-! # Conversion of the concrete degree scale to the reciprocal logarithmic scale -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalLogComparison
open ReciprocalParameterChoice ReciprocalMomentDeficit

def prefixDecay : ℝ := decayConstant/4

theorem prefixDecay_pos : 0 < prefixDecay := div_pos decayConstant_pos (by norm_num)

theorem prefixDecay_le_one : prefixDecay ≤ 1 := by
  unfold prefixDecay
  linarith [decayConstant_le]

theorem degreeScale_square_le (ρ : ℝ) (hρ : 3/2 ≤ ρ) :
    (degreeScale ρ:ℝ)^2 ≤ 4*ρ^2 := by
  obtain ⟨_,_,hhi⟩ := degreeScale_bounds ρ hρ
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (degreeScale ρ))
    (show (degreeScale ρ:ℝ) ≤ 2*ρ by linarith) 2
  nlinarith

theorem decay_to_logarithmic (L R ρ : ℝ) (hL : 0 < L) (hρ : 3/2 ≤ ρ)
    (hR : R = ρ*L) :
    Real.exp (-decayConstant*L/(degreeScale ρ:ℝ)^2) ≤
      Real.exp (-prefixDecay*L^3/R^2) := by
  obtain ⟨hm,_,_⟩ := degreeScale_bounds ρ hρ
  have hm0 : (0:ℝ) < (degreeScale ρ:ℝ)^2 := by
    have : (0:ℝ) < degreeScale ρ := by exact_mod_cast (show 0 < degreeScale ρ by omega)
    positivity
  have hρ0 : 0 < ρ := by linarith
  have hd := div_le_div_of_nonneg_left (mul_nonneg decayConstant_pos.le hL.le)
    hm0 (degreeScale_square_le ρ hρ)
  have he : prefixDecay*L^3/R^2 = decayConstant*L/(4*ρ^2) := by
    rw [hR]
    dsimp [prefixDecay]
    field_simp
  apply Real.exp_le_exp.mpr
  rw [show -prefixDecay*L^3/R^2 = -(prefixDecay*L^3/R^2) by ring,he,
    show -decayConstant*L/(degreeScale ρ:ℝ)^2 =
      -(decayConstant*L/(degreeScale ρ:ℝ)^2) by ring]
  exact neg_le_neg hd

theorem log_ratio_lower (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hL : 4096 ≤ Real.log P) (hQlarge : P^2 < 2*Q) :
    3/2 ≤ Real.log Q/Real.log P := by
  have hL0 : 0 < Real.log P := by linarith
  have hlog := Real.log_lt_log (sq_pos_of_pos hP) hQlarge
  rw [Real.log_pow,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hQ.ne'] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have h2 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)
  apply (le_div_iff₀ hL0).mpr
  linarith

end NField.Alignment.ReciprocalLogComparison
