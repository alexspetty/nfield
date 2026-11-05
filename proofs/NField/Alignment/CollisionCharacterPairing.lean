/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterEigenvectors

/-! # Real character pairs and the actual primitive Fourier functional -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCharacterPairing

open scoped BigOperators ComplexConjugate
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionOdometerRecurrence
open CollisionCharacterEigenvectors CollisionPrimitiveFourier DedekindFourierMoment
open CollisionPotentialSpectralMoments CollisionRamanujan CollisionJordanVariance

theorem characterReVector_coe (q a : ℕ) [NeZero q] :
    (fun x => characterReVector q a x) =ᵐ[phaseHaar] (fun x => (characterMap q a x).re) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (characterReMap q a)

theorem characterImVector_coe (q a : ℕ) [NeZero q] :
    (fun x => characterImVector q a x) =ᵐ[phaseHaar] (fun x => (characterMap q a x).im) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (characterImMap q a)

theorem character_combination_re_coe (q a : ℕ) [NeZero q] (c : ℂ) :
    (fun x => (c.re • characterReVector q a-c.im • characterImVector q a) x) =ᵐ[phaseHaar]
      (fun x => (c*characterMap q a x).re) := by
  have hr := characterReVector_coe q a
  have hi := characterImVector_coe q a
  filter_upwards [Lp.coeFn_sub (c.re • characterReVector q a) (c.im • characterImVector q a),
    Lp.coeFn_smul c.re (characterReVector q a), Lp.coeFn_smul c.im (characterImVector q a),
    hr, hi] with x hx hxr hxi hrx hix
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hxr hxi
  rw [hx, hxr, hxi, hrx, hix]
  rfl

theorem character_combination_im_coe (q a : ℕ) [NeZero q] (c : ℂ) :
    (fun x => (c.im • characterReVector q a+c.re • characterImVector q a) x) =ᵐ[phaseHaar]
      (fun x => (c*characterMap q a x).im) := by
  have hr := characterReVector_coe q a
  have hi := characterImVector_coe q a
  filter_upwards [Lp.coeFn_add (c.im • characterReVector q a) (c.re • characterImVector q a),
    Lp.coeFn_smul c.im (characterReVector q a), Lp.coeFn_smul c.re (characterImVector q a),
    hr, hi] with x hx hxr hxi hrx hix
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hxr hxi
  rw [hx, hxr, hxi, hrx, hix]
  exact add_comm _ _

theorem character_eigenpair_vectors (q a : ℕ) [NeZero q] (U W : HaarL2)
    (hU : shift 1 U=(characterRoot q a).re • U-(characterRoot q a).im • W)
    (hW : shift 1 W=(characterRoot q a).im • U+(characterRoot q a).re • W) :
    ∃ c : ℂ, U=c.re • characterReVector q a-c.im • characterImVector q a ∧
      W=c.im • characterReVector q a+c.re • characterImVector q a := by
  obtain ⟨c,hc⟩ := character_eigenpair_simple q a U W hU hW
  refine ⟨c, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [hc, character_combination_re_coe q a c] with x hx hcx
    have hr := congrArg Complex.re hx
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_self, add_zero] at hr
    exact hr.trans hcx.symm
  · apply Lp.ext
    filter_upwards [hc, character_combination_im_coe q a c] with x hx hcx
    have hi := congrArg Complex.im hx
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact hi.trans hcx.symm

theorem negativeRoot_pow_phase (q a r : ℕ) :
    negativeRoot q a^r=phase q (-(r : ℤ)) a := by
  induction r with
  | zero => simp [phase_zero]
  | succ r ih =>
    rw [pow_succ, ih, negativeRoot_phase, ← phase_add]
    congr 1
    omega

theorem characterMap_conj (q a : ℕ) [NeZero q] (x : Phase) :
    conj (characterMap q a x)=negativeRoot q a^(residueHom q x).toAdd.val := by
  rw [characterMap_phase, phase_conj, negativeRoot_pow_phase]

theorem inner_character_re (q a : ℕ) [NeZero q] (V : HaarL2) :
    inner ℝ V (characterReVector q a)=∫ x, V x*(characterMap q a x).re ∂phaseHaar := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [characterReVector_coe q a] with x hx
  change inner ℝ (V x) (characterReVector q a x)=_
  rw [hx]
  exact mul_comm _ _

theorem inner_character_im (q a : ℕ) [NeZero q] (V : HaarL2) :
    inner ℝ V (characterImVector q a)=∫ x, V x*(characterMap q a x).im ∂phaseHaar := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [characterImVector_coe q a] with x hx
  change inner ℝ (V x) (characterImVector q a x)=_
  rw [hx]
  exact mul_comm _ _

theorem fourierFunctional_character_pair (q a : ℕ) [NeZero q] (V : HaarL2) :
    fourierFunctional q a V=(inner ℝ V (characterReVector q a) : ℂ)-
      Complex.I*(inner ℝ V (characterImVector q a) : ℂ) := by
  have hr : Integrable (fun x => V x*(characterMap q a x).re) phaseHaar := by
    apply (L2.integrable_inner (𝕜 := ℝ) V (characterReVector q a)).congr
    filter_upwards [characterReVector_coe q a] with x hx
    change inner ℝ (V x) (characterReVector q a x)=_
    rw [hx]
    exact mul_comm _ _
  have hi : Integrable (fun x => V x*(characterMap q a x).im) phaseHaar := by
    apply (L2.integrable_inner (𝕜 := ℝ) V (characterImVector q a)).congr
    filter_upwards [characterImVector_coe q a] with x hx
    change inner ℝ (V x) (characterImVector q a x)=_
    rw [hx]
    exact mul_comm _ _
  have hrC : Integrable (fun x => ((V x*(characterMap q a x).re : ℝ) : ℂ)) phaseHaar :=
    Complex.ofRealCLM.integrable_comp hr
  have hiC : Integrable (fun x => ((V x*(characterMap q a x).im : ℝ) : ℂ)) phaseHaar :=
    Complex.ofRealCLM.integrable_comp hi
  rw [fourierFunctional_integral (Nat.pos_of_ne_zero (NeZero.ne q))]
  simp_rw [← characterMap_conj]
  have hf : (fun x => (V x : ℂ)*conj (characterMap q a x))=
      (fun x => ((V x*(characterMap q a x).re : ℝ) : ℂ)-
        Complex.I*((V x*(characterMap q a x).im : ℝ) : ℂ)) := by
    funext x
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hf, integral_sub hrC (hiC.const_mul Complex.I), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, ← inner_character_re,
    ← inner_character_im]

theorem increment_character_pair {q a : ℕ} [NeZero q] (hq : 2 ≤ q) (ha : a.Coprime q) :
    inner ℝ incrementVector (characterReVector q a)= -2*amplitude q/3 ∧
      inner ℝ incrementVector (characterImVector q a)=0 := by
  have hf := incrementVector_fourier hq ha
  rw [fourierFunctional_character_pair] at hf
  constructor
  · have hr := congrArg Complex.re hf
    simp at hr
    linarith
  · have hi := congrArg Complex.im hf
    simpa using hi

end NField.Alignment.CollisionCharacterPairing
