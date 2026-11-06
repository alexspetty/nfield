/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandParameters
import NField.Alignment.CommonResetNegativeCurvature

/-! # The original signed conductor summands and their exact completed phases -/

noncomputable section

namespace NField.Alignment.CommonResetBandPhases

open scoped BigOperators
open CommonResetBandParameters CommonResetInverseReciprocity CommonResetDerivativeFirst
open CommonResetAmplitude CommonResetEndpointTailRows CommonResetTailWeights
open InverseAdditiveCompletion CommonResetNegativeCurvature DedekindInverseResidueTransform

def bandFrequency (p u v j : ℕ) : ZMod u := -((p : ZMod u)^2*j*v)

def gatedPhase (p t u v : ℕ) (η : ℤ) (j : ℕ) : ℝ :=
  if u.Coprime t then phaseTerm p t u v η j else 0

theorem phaseTerm_as_phase_im {p t u v : ℕ} (ht : 0 < t) (η : ℤ) (j : ℕ) :
    phaseTerm p t u v η j = (if η=0 then 1 else -1 : ℝ)*
      ((bandAmplitude (η == 0) t u v j : ℂ)*
        phase (((p : ℝ)^2*j*v)*inverseResidue u t/t + (η : ℝ)*j*((p : ℝ)-1/2)/t)).im := by
  rw [phaseTerm_literal ht]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, phase_im]
  have he : 2*Real.pi*((p : ℝ)^2*j*v*inverseResidue u t/t+(η : ℝ)*j*((p : ℝ)-1/2)/t) =
      2*Real.pi*(j : ℝ)*(p : ℝ)^2*(v : ℝ)*(inverseResidue u t : ℝ)/(t : ℝ)+
        (η : ℝ)*(2*(p : ℝ)-1)*halfAngle t j := by unfold halfAngle; ring
  rw [he]
  by_cases hη : η=0 <;> simp only [phaseCoefficient, bandAmplitude, hη, beq_iff_eq, if_true, if_false] <;> ring

/-- Title: `Each original linked phase is exactly the weighted completed reciprocal character`. -/
theorem gatedPhase_completed {p t u v : ℕ} [NeZero u] (ht : 0 < t) (η : ℤ) (j : ℕ) :
    gatedPhase p t u v η j = (if η=0 then 1 else -1 : ℝ)*
      ((bandAmplitude (η == 0) t u v j : ℂ)*
        (inversePhase 1 (bandFrequency p u v j) (t : ZMod u)*
          phase (reciprocalCoefficient p u v j η/t))).im := by
  by_cases hcop : u.Coprime t
  · rw [gatedPhase, if_pos hcop, phaseTerm_as_phase_im ht]
    have hr := inverse_reciprocity_completion ht hcop ((p : ℤ)^2*j*v)
      ((η : ℝ)*j*((p : ℝ)-1/2))
    push_cast at hr
    simpa only [bandFrequency, reciprocalCoefficient] using
      congrArg (fun z : ℂ => (if η=0 then 1 else -1 : ℝ)*
        ((bandAmplitude (η == 0) t u v j : ℂ)*z).im) hr
  · rw [gatedPhase, if_neg hcop, inverse_phase_natCast,
      dif_neg (show ¬ t.Coprime u from fun h => hcop h.symm)]
    simp only [zero_mul, mul_zero, Complex.zero_im]

/-- Title: `Prime-square multiplication leaves precisely the printed product-frequency gcd`. -/
theorem bandFrequency_gcd {p u : ℕ} [NeZero u] (hp : p.Prime) (hup : u < p) (v j : ℕ) :
    (bandFrequency p u v j).val.gcd u = (j*v).gcd u := by
  have hcop : p.Coprime u := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hup) (Nat.le_of_dvd (NeZero.pos u) hd))
  have hunit : IsUnit (p : ZMod u) := (ZMod.isUnit_iff_coprime p u).mpr hcop
  have he : (p : ZMod u)^2*j*v = ((j*v : ℕ) : ZMod u)*(p : ZMod u)^2 := by push_cast; ring
  unfold bandFrequency
  rw [gcd_neg_val, he, PrimePowerGcdBound.gcd_val_mul_unit u _ _ (hunit.pow 2),
    ZMod.val_natCast]
  exact (Nat.mod_modEq (j*v) u).gcd_eq

end NField.Alignment.CommonResetBandPhases
