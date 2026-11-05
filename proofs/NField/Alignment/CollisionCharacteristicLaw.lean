/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialLpConvergence
import NField.Alignment.CollisionPotentialReflection
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The characteristic function of the actual Haar potential
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCharacteristicLaw

open scoped Classical ENNReal ComplexConjugate
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialMoments CollisionPotentialReflection

def potentialCharacteristic (t : ℝ) : ℂ := charFun (Measure.map collisionPotential phaseHaar) t

theorem potentialCharacteristic_integral (t : ℝ) :
    potentialCharacteristic t=
      ∫ x, Complex.exp (((t*collisionPotential x : ℝ) : ℂ)*Complex.I) ∂phaseHaar := by
  rw [potentialCharacteristic,charFun_apply_real,
    integral_map (Lp.aestronglyMeasurable collisionPotential).aemeasurable (by fun_prop)]
  simp only [Complex.ofReal_mul]

theorem potential_law_memLp (k : ℕ) :
    MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (Measure.map collisionPotential phaseHaar) := by
  apply (memLp_map_measure_iff (by fun_prop)
    (Lp.aestronglyMeasurable collisionPotential).aemeasurable).mpr
  simpa only [Function.comp_def,id_eq] using potential_memLp_finite (k : ℝ≥0∞) (by simp)

theorem potentialCharacteristic_smooth : ContDiff ℝ (⊤ : ℕ∞) potentialCharacteristic := by
  exact contDiff_charFun' potential_law_memLp

theorem potentialCharacteristic_even (t : ℝ) :
    potentialCharacteristic (-t)=potentialCharacteristic t := by
  have h := charFun_map_mul_comp (Lp.aestronglyMeasurable collisionPotential).aemeasurable (-1) t
  simp only [neg_one_mul,collisionPotential_law_symmetric] at h
  exact h.symm

theorem potentialCharacteristic_real (t : ℝ) : (potentialCharacteristic t).im=0 := by
  have h := charFun_neg (μ := Measure.map collisionPotential phaseHaar) t
  change potentialCharacteristic (-t)=conj (potentialCharacteristic t) at h
  rw [potentialCharacteristic_even] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem imaginary_exponential_difference (t x y : ℝ) :
    ‖Complex.exp (((t*x : ℝ) : ℂ)*Complex.I)-
      Complex.exp (((t*y : ℝ) : ℂ)*Complex.I)‖ ≤ |t| * |x-y| := by
  have he : Complex.exp (((t*x : ℝ) : ℂ)*Complex.I)-
      Complex.exp (((t*y : ℝ) : ℂ)*Complex.I)=
      Complex.exp (((t*y : ℝ) : ℂ)*Complex.I)*
        (Complex.exp (Complex.I*((t*(x-y) : ℝ) : ℂ))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  simpa only [Real.norm_eq_abs,abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(x-y)))

theorem imaginary_exponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (t : ℝ) :
    Integrable (fun x => Complex.exp (((t*F x : ℝ) : ℂ)*Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simp only [Complex.norm_exp_ofReal_mul_I,le_refl])

theorem characteristic_difference_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F G : Ω → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ) (t : ℝ) :
    ‖(∫ x, Complex.exp (((t*F x : ℝ) : ℂ)*Complex.I) ∂μ)-
      (∫ x, Complex.exp (((t*G x : ℝ) : ℂ)*Complex.I) ∂μ)‖ ≤
      |t| * (∫ x, |F x-G x| ∂μ) := by
  have hEF := imaginary_exponential_integrable F hF.aestronglyMeasurable t
  have hEG := imaginary_exponential_integrable G hG.aestronglyMeasurable t
  rw [← integral_sub hEF hEG]
  calc
    _ ≤ ∫ x, ‖Complex.exp (((t*F x : ℝ) : ℂ)*Complex.I)-
      Complex.exp (((t*G x : ℝ) : ℂ)*Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| * |F x-G x| ∂μ := integral_mono (hEF.sub hEG).norm
      ((hF.sub hG).abs.const_mul |t|) (fun x => imaginary_exponential_difference t (F x) (G x))
    _ = _ := integral_const_mul _ _

end NField.Alignment.CollisionCharacteristicLaw
