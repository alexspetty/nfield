/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalSelectedProduct
import NField.Alignment.ReciprocalMomentDeficit
import NField.Alignment.RealPolynomialExponentialBound

/-! # Uniform decay of the literal reciprocal Taylor polynomial -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalPolynomialDecay
open RealPolynomialMomentBox ReciprocalPolynomialCoefficients ReciprocalSelectedProduct
  ReciprocalParameterChoice ReciprocalMomentDeficit RealPolynomialExponentialBound

theorem reciprocal_polynomial_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P Q x L ρ : ℝ),
      0 < P → 0 < Q → 4096 ≤ L → Real.log P = L →
      3/2 ≤ ρ → Real.log Q = ρ*L → P ≤ x → x ≤ 3*P →
      ‖polynomialBilinear
          (coefficient Q x (n:=degree (degreeScale ρ))) (shiftLength L)‖ ≤
        (shiftLength L:ℝ)^2*C*
          Real.exp (-decayConstant*L/(degreeScale ρ:ℝ)^2) := by
  obtain ⟨A,hA,hpoly⟩ := polynomial_exponential_bound
  refine ⟨Real.exp (A/2+126),Real.one_le_exp (by linarith),?_⟩
  intro P Q x L ρ hP hQ hL hlogP hρ hlogQ hx0 hx1
  have hL0 : 0 ≤ L := by linarith
  have hx : 0 < x := hP.trans_le hx0
  obtain ⟨hm,hm0,hm1⟩ := degreeScale_bounds ρ hρ
  obtain ⟨hn,hnm,hns,hs⟩ := degree_moment_bounds (degreeScale ρ) hm
  obtain ⟨hH,_,_⟩ := shiftLength_bounds L hL
  obtain ⟨hHlo,hHhi⟩ := shiftLength_log_bounds L hL
  obtain ⟨hxlo,hxhi,hscale⟩ := block_log_bounds P x L hP hL hlogP hx0 hx1
  have hprod := reciprocal_saving_product Q x L ρ hQ hx hL0 hρ
    (degreeScale ρ) hm hm0 hm1 hlogQ hxlo hxhi hscale
    (momentOrder (degreeScale ρ)) (shiftLength L) (degree (degreeScale ρ))
    hs hH hnm hHlo
  have hp := hpoly (degree (degreeScale ρ)) (momentOrder (degreeScale ρ)) (shiftLength L)
    (coefficient Q x) ((degreeScale ρ:ℝ)^2*L/128) hn hns hH
    (coefficient_ne_zero Q x hQ.ne' hx.ne') (by simpa only [neg_div,neg_mul] using hprod)
  have hdef := deficit_exponent_bound (degreeScale ρ) hm L
    (Real.log (shiftLength L:ℝ)) hL0 (by linarith)
  change (4*deficit (degreeScale ρ)*Real.log (shiftLength L:ℝ)-
    (degreeScale ρ:ℝ)^2*L/128)/(8*(momentOrder (degreeScale ρ):ℝ)^2) ≤ _ at hdef
  change ‖polynomialBilinear (coefficient Q x) (shiftLength L)‖ ≤
    (shiftLength L:ℝ)^2*Real.exp (A/2+126+
      (4*deficit (degreeScale ρ)*Real.log (shiftLength L:ℝ)-
        (degreeScale ρ:ℝ)^2*L/128)/(8*(momentOrder (degreeScale ρ):ℝ)^2)) at hp
  calc
    _ ≤ (shiftLength L:ℝ)^2*Real.exp (A/2+126+
        (4*deficit (degreeScale ρ)*Real.log (shiftLength L:ℝ)-
          (degreeScale ρ:ℝ)^2*L/128)/(8*(momentOrder (degreeScale ρ):ℝ)^2)) := hp
    _ ≤ (shiftLength L:ℝ)^2*Real.exp (A/2+126+
        (-decayConstant*L/(degreeScale ρ:ℝ)^2)) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

end NField.Alignment.ReciprocalPolynomialDecay
