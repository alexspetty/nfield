/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeTwist

/-!
# The literal centered twist and square-root variance chain

This exposes the intermediate equalities and all three inequalities in
the variance proof, not just their final squared consequence.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeVarianceDisplays
open scoped BigOperators
open SpectralRepulsion FiniteMagnitudeDecorrelation PrimeSquareMagnitudeFamily
  MagnitudeMomentArithmetic

theorem complex_average_re {ι : Type*} [Fintype ι] (F : ι → ℂ) :
    ((Fintype.card ι : ℂ)⁻¹*∑ i, F i).re = uniformAverage (fun i => (F i).re) := by
  have hc : (Fintype.card ι : ℂ)⁻¹ = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc]
  simp [uniformAverage,Complex.mul_re]

theorem real_twist_inputs {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    uniformAverage (fun χ : PrimitiveOddFamily p => (χ.val (2 : ZMod (p^2))).re) = 0 ∧
    (∀ χ : PrimitiveOddFamily p, |(χ.val (2 : ZMod (p^2))).re| ≤ 1) ∧
    uniformAverage (fun χ : PrimitiveOddFamily p =>
      lMagnitude p χ^2*(χ.val (2 : ZMod (p^2))).re) = marginalL p/2 := by
  refine ⟨?_,?_,?_⟩
  · have h := congrArg Complex.re (character_two_mean hp hp5)
    rw [complex_average_re] at h
    exact h
  · intro χ
    exact (Complex.abs_re_le_norm _).trans (χ.val.norm_le_one _)
  · have h := congrArg Complex.re (l_magnitude_twist hp hp5)
    rw [complex_average_re] at h
    simpa [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,pow_two] using h

theorem centered_twist_chain {ι : Type*} [Fintype ι] [Nonempty ι]
    (Y Z : ι → ℝ) {ν : ℝ} (hν : 0 ≤ ν)
    (hsecond : uniformAverage (fun i => Y i^2) = ν)
    (hzero : uniformAverage Z = 0) (hbound : ∀ i, |Z i| ≤ 1)
    (htwist : uniformAverage (fun i => Y i^2*Z i) = ν/2) :
    let c := uniformAverage Y
    ν/2 = uniformAverage (fun i => (Y i-c)*(Y i+c)*Z i) ∧
    ν/2 ≤ Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun i => (Y i+c)^2*Z i^2)) ∧
    Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun i => (Y i+c)^2*Z i^2)) ≤
      Real.sqrt (uniformVariance Y)*Real.sqrt (ν+3*c^2) ∧
    Real.sqrt (uniformVariance Y)*Real.sqrt (ν+3*c^2) ≤ 2*Real.sqrt (ν*uniformVariance Y) := by
  dsimp only
  let c := uniformAverage Y
  have hc : c^2 ≤ ν := by simpa [c,hsecond] using average_sq_le Y
  have hfactor : uniformAverage (fun i => (Y i-c)*(Y i+c)*Z i) = ν/2 := by
    have heq : (fun i => (Y i-c)*(Y i+c)*Z i) =
        (fun i => Y i^2*Z i-c^2*Z i) := by funext i; ring
    rw [heq,average_sub,uniformAverage_mul_left,htwist,hzero]
    ring
  have hplus : uniformAverage (fun i => (Y i+c)^2) = ν+3*c^2 := by
    have heq : (fun i => (Y i+c)^2) =
        (fun i => Y i^2+(2*c)*Y i+c^2) := by funext i; ring
    rw [heq,uniformAverage_add,uniformAverage_add,uniformAverage_mul_left,average_const,hsecond]
    dsimp [c]
    ring
  have hb : uniformAverage (fun i => (Y i+c)^2*Z i^2) ≤ ν+3*c^2 := by
    rw [← hplus]
    apply average_mono
    intro i
    have hz := hbound i
    rw [abs_le] at hz
    have hz2 : Z i^2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hz2 (sq_nonneg (Y i+c))
  have hv := variance_nonneg Y
  have he : 0 ≤ uniformAverage (fun i => (Y i+c)^2*Z i^2) := average_nonneg (by intro i; positivity)
  have hcs := average_cauchy_sq (fun i => Y i-c) (fun i => (Y i+c)*Z i)
  have hcs' : (ν/2)^2 ≤ uniformVariance Y*uniformAverage (fun i => (Y i+c)^2*Z i^2) := by
    simpa only [← mul_assoc,hfactor,mul_pow,uniformVariance,c] using hcs
  have hp2 : (Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun i => (Y i+c)^2*Z i^2)))^2 =
      uniformVariance Y*uniformAverage (fun i => (Y i+c)^2*Z i^2) := by
    rw [mul_pow,Real.sq_sqrt hv,Real.sq_sqrt he]
  refine ⟨hfactor.symm,?_,?_,?_⟩
  · have hprod : 0 ≤ Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun i => (Y i+c)^2*Z i^2)) := by positivity
    nlinarith
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
  · calc
      _ ≤ Real.sqrt (uniformVariance Y)*Real.sqrt (4*ν) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),Real.sqrt_mul hν]
        norm_num
        ring

theorem actual_centered_twist_chain {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let Y := lMagnitude p
    let Z := fun χ : PrimitiveOddFamily p => (χ.val (2 : ZMod (p^2))).re
    let c := uniformAverage Y
    marginalL p/2 = uniformAverage (fun χ => (Y χ-c)*(Y χ+c)*Z χ) ∧
    marginalL p/2 ≤ Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun χ => (Y χ+c)^2*Z χ^2)) ∧
    Real.sqrt (uniformVariance Y)*Real.sqrt (uniformAverage (fun χ => (Y χ+c)^2*Z χ^2)) ≤
      Real.sqrt (uniformVariance Y)*Real.sqrt (marginalL p+3*c^2) ∧
    Real.sqrt (uniformVariance Y)*Real.sqrt (marginalL p+3*c^2) ≤ 2*Real.sqrt (marginalL p*uniformVariance Y) := by
  letI := family_nonempty hp (by omega)
  obtain ⟨hz,hb,ht⟩ := real_twist_inputs hp hp5
  exact centered_twist_chain _ _ (marginal_positive (p : ℝ) (by exact_mod_cast hp.one_lt)).le
    (l_magnitude_second_moment hp (by omega)) hz hb ht

end NField.Alignment.MagnitudeVarianceDisplays
