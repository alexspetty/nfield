/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRandomEulerProduct
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Integrability of the actual random Euler-product integral

The finite-prime product is jointly measurable on a vertical line and
the Steinhaus phase space. Its positive Euler-product norm bound gives
a Cauchy-kernel majorant. Both line and phase integrability, and joint
integrability for Fubini, are proved for every positive line real part.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperEulerIntegral

open scoped BigOperators Topology
open MeasureTheory SteinhausMoment HarperRandomEulerProduct HarperSmoothCount
  CollisionMertensInput

def linePoint (sigma t : ℝ) : ℂ := (sigma : ℂ)+(t : ℂ)*Complex.I
def cauchyWeight (sigma t : ℝ) : ℝ := (sigma^2+t^2)⁻¹
def spectralDensity (P sigma : ℝ) (z : ℝ × PhaseSpace) : ℝ :=
  ‖eulerProduct P (linePoint sigma z.1) z.2‖^2 * cauchyWeight sigma z.1
def spectralIntegral (P sigma : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ t : ℝ, spectralDensity P sigma (t,ω)

theorem linePoint_re (sigma t : ℝ) : (linePoint sigma t).re = sigma := by
  simp [linePoint]

theorem linePoint_norm_sq (sigma t : ℝ) : ‖linePoint sigma t‖^2 = sigma^2+t^2 := by
  rw [Complex.sq_norm]
  simp [linePoint, Complex.normSq_apply, pow_two]

theorem cauchyWeight_nonneg (sigma t : ℝ) : 0 ≤ cauchyWeight sigma t := by
  unfold cauchyWeight
  positivity

theorem cauchyWeight_scaled {sigma : ℝ} (hs : 0 < sigma) (t : ℝ) :
    cauchyWeight sigma t = (sigma^2)⁻¹ * (1+(t/sigma)^2)⁻¹ := by
  have hd : sigma^2+t^2 ≠ 0 := by positivity
  have hu : 1+(t/sigma)^2 ≠ 0 := by positivity
  unfold cauchyWeight
  field_simp

theorem cauchyWeight_integrable {sigma : ℝ} (hs : 0 < sigma) :
    Integrable (cauchyWeight sigma) volume := by
  have h := integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero hs.ne')
  have he : cauchyWeight sigma = fun t : ℝ => (sigma^2)⁻¹ * (1+(t*sigma⁻¹)^2)⁻¹ := by
    funext t
    simpa only [div_eq_mul_inv] using cauchyWeight_scaled hs t
  rw [he]
  exact h.const_mul _

theorem verticalProduct_measurable (P sigma : ℝ) :
    Measurable (fun z : ℝ × PhaseSpace => eulerProduct P (linePoint sigma z.1) z.2) := by
  apply Finset.measurable_prod
  intro q hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (primesUpTo_mem.mp hq).1.ne_zero
  have hc : Continuous (fun z : ℝ × PhaseSpace => (q : ℂ)^(linePoint sigma z.1)) :=
    (show Continuous (fun z : ℝ × PhaseSpace => linePoint sigma z.1) by
      unfold linePoint
      fun_prop).const_cpow (Or.inl hq0)
  exact (measurable_const.sub (((steinhaus_measurable q).comp measurable_snd).div hc.measurable)).inv

theorem spectralDensity_measurable (P sigma : ℝ) : Measurable (spectralDensity P sigma) :=
  ((verticalProduct_measurable P sigma).norm.pow_const 2).mul
    ((measurable_const.add (measurable_fst.pow_const 2)).inv)

theorem spectralDensity_nonneg (P sigma : ℝ) (z : ℝ × PhaseSpace) :
    0 ≤ spectralDensity P sigma z := mul_nonneg (sq_nonneg _) (cauchyWeight_nonneg _ _)

theorem spectralDensity_bound (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) (z : ℝ × PhaseSpace) :
    spectralDensity P sigma z ≤ (shiftedProduct P sigma)^2 * cauchyWeight sigma z.1 := by
  apply mul_le_mul_of_nonneg_right _ (cauchyWeight_nonneg _ _)
  have h := eulerProduct_norm_le P (s := linePoint sigma z.1) (by rwa [linePoint_re]) z.2
  rw [linePoint_re] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem spectralDensity_integrable (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    Integrable (spectralDensity P sigma) (volume.prod phaseMeasure) := by
  apply ((cauchyWeight_integrable hs).const_mul ((shiftedProduct P sigma)^2)).comp_fst phaseMeasure |>.mono'
    (spectralDensity_measurable P sigma).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (spectralDensity_nonneg P sigma z)]
  exact spectralDensity_bound P hs z

theorem spectralDensity_integrable_phase (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) (t : ℝ) :
    Integrable (fun ω => spectralDensity P sigma (t,ω)) phaseMeasure := by
  apply Integrable.of_bound
    ((spectralDensity_measurable P sigma).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((shiftedProduct P sigma)^2*cauchyWeight sigma t)
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.norm_of_nonneg (spectralDensity_nonneg P sigma (t,ω))]
  exact spectralDensity_bound P hs (t,ω)

theorem spectralDensity_integrable_line (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) (ω : PhaseSpace) :
    Integrable (fun t => spectralDensity P sigma (t,ω)) volume := by
  apply ((cauchyWeight_integrable hs).const_mul ((shiftedProduct P sigma)^2)).mono'
    ((spectralDensity_measurable P sigma).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.norm_of_nonneg (spectralDensity_nonneg P sigma (t,ω))]
  exact spectralDensity_bound P hs (t,ω)

theorem spectralIntegral_integrable (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    Integrable (spectralIntegral P sigma) phaseMeasure :=
  (spectralDensity_integrable P hs).integral_prod_right

theorem spectralIntegral_nonneg (P sigma : ℝ) (ω : PhaseSpace) :
    0 ≤ spectralIntegral P sigma ω := integral_nonneg (fun t => spectralDensity_nonneg _ _ (t,ω))

theorem spectralDensity_eq (P sigma t : ℝ) (ω : PhaseSpace) :
    spectralDensity P sigma (t,ω) =
      ‖eulerProduct P (linePoint sigma t) ω‖^2 / ‖linePoint sigma t‖^2 := by
  rw [linePoint_norm_sq, div_eq_mul_inv]
  rfl

end NField.Alignment.HarperEulerIntegral
