/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalMomentDeficit

/-! # The finite reciprocal Taylor remainder and shift loss are smaller -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalTaylorDecay
open ReciprocalParameterChoice ReciprocalMomentDeficit

theorem shift_ratio_bound (P L : ℝ) (hP : 0 < P) (hL : 4096 ≤ L)
    (hlogP : Real.log P = L) :
    (shiftLength L:ℝ)^2/P ≤ Real.exp (-L/32) := by
  obtain ⟨_,_,hH⟩ := shiftLength_bounds L hL
  have hp : P = Real.exp L := by rw [← hlogP,Real.exp_log hP]
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (shiftLength L)) hH 2
  have h := div_le_div_of_nonneg_right hh hP.le
  rw [hp,← Real.exp_nat_mul,← Real.exp_sub] at h
  convert h using 1 <;> congr 1 <;> ring

theorem reciprocal_remainder_decay (P Q x L ρ : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hL : 4096 ≤ L) (hlogP : Real.log P = L) (hlogQ : Real.log Q = ρ*L)
    (hρ : 3/2 ≤ ρ) (hx : P ≤ x) :
    Q/x*((shiftLength L:ℝ)^2/x)^(degree (degreeScale ρ)+1) ≤ Real.exp (-L) := by
  have hx0 : 0 < x := hP.trans_le hx
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hm,hm0,hm1⟩ := degreeScale_bounds ρ hρ
  have hr := shift_ratio_bound P L hP hL hlogP
  have hq : Q/P = Real.exp ((ρ-1)*L) := by
    rw [show Q = Real.exp (ρ*L) by rw [← hlogQ,Real.exp_log hQ],
      show P = Real.exp L by rw [← hlogP,Real.exp_log hP],← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ Q/P*((shiftLength L:ℝ)^2/P)^(degree (degreeScale ρ)+1) := by
      gcongr
    _ ≤ Real.exp ((ρ-1)*L)*(Real.exp (-L/32))^(degree (degreeScale ρ)+1) := by
      rw [← hq]
      gcongr
    _ = Real.exp (((ρ-1)-(degree (degreeScale ρ)+1:ℕ)/32)*L) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp [degree]
      push_cast
      have h := mul_nonneg (show 0 ≤ 2*(degreeScale ρ:ℝ)-ρ by linarith) hL0
      nlinarith

theorem small_error_decay (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (-L) ≤ Real.exp (-decayConstant*L/(m:ℝ)^2) ∧
    Real.exp (-L/32) ≤ Real.exp (-decayConstant*L/(m:ℝ)^2) := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < (m:ℝ)^2 := by positivity
  have hc : decayConstant/(m:ℝ)^2 ≤ 1/32 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith [decayConstant_le,sq_nonneg ((m:ℝ)-1)]
  have hex : -L/32 ≤ -decayConstant*L/(m:ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hc hL
    rw [show -decayConstant*L/(m:ℝ)^2 = -(decayConstant/(m:ℝ)^2*L) by ring]
    linarith
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_exp.mpr hex

end NField.Alignment.ReciprocalTaylorDecay
