/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoughOrthogonality

/-!
# Grouping weighted second moments by their canonical rough part

Expand finite weighted Steinhaus squares, use the proved weighted
orthogonality, and recombine each surviving fiber into a squared smooth sum.
Every interchange with the integral is justified by integrability.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRoughMoment

open scoped BigOperators
open MeasureTheory SteinhausMoment SteinhausCoordinates HarperSmoothRough
  HarperRoughOrthogonality HarperActualConditioning HarperRoundedCutoff
  HarperProductApproximation HarperParameterBounds CollisionMertensInput

theorem same_fiber_pair_sum (s : Finset ℕ) (r : ℕ → ℕ) (c : ℕ → ℕ → ℂ) :
    (∑ u ∈ s, ∑ v ∈ s, if r u = r v then c u v else 0) =
      ∑ m ∈ s.image r, ∑ u ∈ s.filter (fun u => r u = m),
        ∑ v ∈ s.filter (fun v => r v = m), c u v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem r hn)
    (fun u => ∑ v ∈ s, if r u = r v then c u v else 0)]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [(Finset.mem_filter.mp hu).2]
  simp only [eq_comm]

theorem weighted_pair_integrable {W : PhaseSpace → ℂ} (hW : Measurable W)
    (hbound : ∀ ω, ‖W ω‖ ≤ 1) (u v : ℕ) :
    Integrable (fun ω => W ω * (steinhaus u ω * star (steinhaus v ω))) phaseMeasure :=
  (steinhaus_pair_integrable u v).bdd_mul hW.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

theorem indexed_pair_expansion (s : Finset ℕ) (w : ℕ → ℂ) (a : ℕ → ℕ)
    (W : ℂ) (ω : PhaseSpace) :
    W * ((∑ u ∈ s, w u * steinhaus (a u) ω) *
      star (∑ v ∈ s, w v * steinhaus (a v) ω)) =
      ∑ u ∈ s, ∑ v ∈ s, (w u * star (w v)) *
        (W * (steinhaus (a u) ω * star (steinhaus (a v) ω))) := by
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem weighted_polynomial_pair_integral (s : Finset ℕ) (w : ℕ → ℂ) (a : ℕ → ℕ)
    {W : PhaseSpace → ℂ} (hW : Measurable W) (hbound : ∀ ω, ‖W ω‖ ≤ 1) :
    (∫ ω, W ω * ((∑ u ∈ s, w u * steinhaus (a u) ω) *
      star (∑ v ∈ s, w v * steinhaus (a v) ω)) ∂phaseMeasure) =
      ∑ u ∈ s, ∑ v ∈ s, (w u * star (w v)) *
        ∫ ω, W ω * (steinhaus (a u) ω * star (steinhaus (a v) ω)) ∂phaseMeasure := by
  have hi (u v : ℕ) := (weighted_pair_integrable hW hbound (a u) (a v)).const_mul
    (w u * star (w v))
  simp_rw [indexed_pair_expansion]
  rw [integral_finsetSum s (fun u _ => integrable_finsetSum s (fun v _ => hi u v))]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_finsetSum s (fun v _ => hi u v)]
  apply Finset.sum_congr rfl
  intro v _
  exact integral_const_mul _ _

theorem weighted_polynomial_rough_decomposition {P : ℝ} (s : Finset ℕ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n) {W : PhaseSpace → ℂ}
    (hW : Measurable W) (hbound : ∀ ω, ‖W ω‖ ≤ 1) (hdep : DependsOn (primesUpTo P) W) :
    (∫ ω, W ω * ((∑ u ∈ s, w u * steinhaus u ω) *
      star (∑ v ∈ s, w v * steinhaus v ω)) ∂phaseMeasure) =
      ∑ m ∈ s.image (roughPart (primeBase P)),
        ∫ ω, W ω * ((∑ u ∈ s.filter (fun u => roughPart (primeBase P) u = m),
          w u * steinhaus (supportedPart (primeBase P) u) ω) *
          star (∑ v ∈ s.filter (fun v => roughPart (primeBase P) v = m),
            w v * steinhaus (supportedPart (primeBase P) v) ω)) ∂phaseMeasure := by
  classical
  have hex := weighted_polynomial_pair_integral s w id hW hbound
  simp only [id_eq] at hex
  rw [hex]
  calc
    _ = ∑ u ∈ s, ∑ v ∈ s,
        if roughPart (primeBase P) u = roughPart (primeBase P) v then
          (w u * star (w v)) * ∫ ω, W ω *
            (steinhaus (supportedPart (primeBase P) u) ω *
              star (steinhaus (supportedPart (primeBase P) v) ω)) ∂phaseMeasure
        else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [weighted_pair_integral (hs u hu) (hs v hv) hW hdep]
      split_ifs <;> simp only [mul_zero]
    _ = _ := by
      rw [same_fiber_pair_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact (weighted_polynomial_pair_integral _ w (supportedPart (primeBase P)) hW hbound).symm

theorem smoothBox_norm_le_one {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (ω : PhaseSpace) :
    ‖(smoothBox p c1 c2 i (fun n => steinhaus n ω) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothBox_nonneg hell c1 c2 i _)]
  exact smoothValue_le_one (precision_pos hell) _ _ _ _ c1 c2 _

/-- The actual box-weighted second moment is a sum over equal rough parts. -/
theorem smoothBox_second_moment_by_rough {p : ℕ}
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (i : Boxes p)
    (s : Finset ℕ) (w : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖^2 *
      smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure) =
      ∑ m ∈ s.image (roughPart (primeBase (primeCutoff ((p : ℝ)-1)))),
        ∫ ω, ‖∑ n ∈ s.filter (fun n =>
            roughPart (primeBase (primeCutoff ((p : ℝ)-1))) n = m),
          w n * steinhaus (supportedPart (primeBase (primeCutoff ((p : ℝ)-1))) n) ω‖^2 *
          smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure := by
  have h := weighted_polynomial_rough_decomposition s w hs
    (W := fun ω => (smoothBox p c1 c2 i (fun n => steinhaus n ω) : ℂ))
    (Complex.continuous_ofReal.measurable.comp (smoothBox_measurable hell c1 c2 i))
    (smoothBox_norm_le_one hell c1 c2 i)
    (fun {_ _} h => congrArg (fun x : ℝ => (x : ℂ))
      (smoothBox_small_coordinates p c1 c2 i h))
  simp_rw [self_pair_eq_norm_sq, ← Complex.ofReal_mul, integral_complex_ofReal] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.re_sum, mul_comm] using hre

end NField.Alignment.HarperRoughMoment
