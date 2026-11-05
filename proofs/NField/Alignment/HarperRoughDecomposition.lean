/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoughMoment
import NField.Alignment.HarperRoughSupport
import NField.Alignment.HarperConditioningFrequencies

/-!
# The literal smooth/rough decomposition of the retained random moment

Group the retained moment by its canonical rough factor and reindex each
fiber as the actual positive P-smooth sum through x/m. The resulting
conditioning sum is the first equality in Harper Section 3.4, for the
constructed weights and frequencies, including cells with zero weight.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRoughDecomposition

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperRoughMoment HarperRoughSupport
  HarperSmoothRough HarperSmoothCount HarperRetainedSum HarperActualConditioning
  HarperRoundedCutoff HarperProductApproximation HarperParameterBounds
  HarperRetainedTransfer HarperConditioningFrequencies

def roughSquare (x P y : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) : ℝ :=
  ∑ m ∈ roughSupport ⌊x⌋₊ P y,
    ‖∑ d ∈ smoothSet (x / (m : ℝ)) P, w (m*d) * steinhaus d ω‖^2

theorem roughSquare_nonneg (x P y : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) :
    0 ≤ roughSquare x P y w ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem weighted_roughSquare_integrable {p : ℕ}
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (i : Boxes p)
    (x P y : ℝ) (w : ℕ → ℂ) :
    Integrable (fun ω => roughSquare x P y w ω *
      smoothBox p c1 c2 i (fun n => steinhaus n ω)) phaseMeasure := by
  simp only [roughSquare, Finset.sum_mul]
  exact integrable_finsetSum _ (fun m _ =>
    random_weighted_smooth_integrable (precision_pos hell) _ _ _ _ i c1 c2
      (fun d => w (m*d)))

theorem retained_moment_sum_decomposition {p : ℕ}
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (i : Boxes p)
    (N : ℕ) (y : ℝ) (hPy : primeCutoff ((p : ℝ)-1) ≤ y) (w : ℕ → ℂ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, retainedCoefficient y w n * steinhaus n ω‖^2 *
      smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure) =
      ∑ m ∈ roughSupport N (primeCutoff ((p : ℝ)-1)) y,
        ∫ ω, ‖∑ d ∈ smoothSet ((N : ℝ)/(m : ℝ)) (primeCutoff ((p : ℝ)-1)),
          w (m*d) * steinhaus d ω‖^2 *
          smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure := by
  have hs : ∀ n ∈ retainedSupport N y, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  simp_rw [retained_sum_eq_support]
  rw [smoothBox_second_moment_by_rough hell c1 c2 i _ w hs, retained_rough_image hPy]
  apply Finset.sum_congr rfl
  intro m hm
  apply integral_congr_ae
  filter_upwards with ω
  rw [smooth_fiber_sum hm w (fun d => steinhaus d ω)]

theorem retained_moment_decomposition {p : ℕ}
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (i : Boxes p)
    (N : ℕ) (y : ℝ) (hPy : primeCutoff ((p : ℝ)-1) ≤ y) (w : ℕ → ℂ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, retainedCoefficient y w n * steinhaus n ω‖^2 *
      smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure) =
      ∫ ω, roughSquare (N : ℝ) (primeCutoff ((p : ℝ)-1)) y w ω *
        smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure := by
  rw [retained_moment_sum_decomposition hell c1 c2 i N y hPy w]
  simp only [roughSquare, Nat.floor_natCast, Finset.sum_mul]
  exact (integral_finsetSum _ (fun m _ =>
    random_weighted_smooth_integrable (precision_pos hell) _ _ _ _ i c1 c2
      (fun d => w (m*d)))).symm

theorem randomMoment_retained_decomposition {p : ℕ} (hp : 1 ≤ p)
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (i : Boxes p)
    (y : ℝ) (hPy : primeCutoff ((p : ℝ)-1) ≤ y) (w : ℕ → ℂ) :
    randomMoment p c1 c2 (retainedCoefficient y w) i =
      ∫ ω, roughSquare ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) y w ω *
        smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure := by
  have he : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by
    simp only [Nat.cast_sub hp, Nat.cast_one]
  simpa only [randomMoment, he] using
    retained_moment_decomposition hell c1 c2 i (p-1) y hPy w

def roughConditioning (p : ℕ) (c1 c2 : Coefficients p) (w : ℕ → ℂ) : ℝ :=
  ∑ i, randomWeight p c1 c2 i *
    ((∫ ω, roughSquare ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
        (smoothCutoff ((p : ℝ)-1)) w ω *
        smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure) /
      randomWeight p c1 c2 i)^(3/4 : ℝ)

theorem random_conditioning_decomposition {p : ℕ} (hp : 1 ≤ p)
    (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hPy : primeCutoff ((p : ℝ)-1) ≤ smoothCutoff ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (w : ℕ → ℂ) :
    randomRetainedConditioning p c1 c2 w = roughConditioning p c1 c2 w := by
  rw [random_conditioning_as_conditional hell, roughConditioning]
  apply Finset.sum_congr rfl
  intro i _
  rw [randomMoment_retained_decomposition hp hell c1 c2 i _ hPy w]

theorem actual_random_decomposition {p : ℕ} (hp : 1 ≤ p)
    (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hPy : primeCutoff ((p : ℝ)-1) ≤ smoothCutoff ((p : ℝ)-1)) :
    actualRandomConditioning p = roughConditioning p
      (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) (fun _ => 1) :=
  random_conditioning_decomposition hp hell hPy _ _ _

/-- At the actual rounded parameters all cutoff hypotheses hold eventually. -/
theorem eventual_actual_random_decomposition : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p = roughConditioning p
      (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) (fun _ => 1) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually eventual_cutoff_hierarchy] with p hp hell hPy
  exact actual_random_decomposition hp hell hPy.1.le

end NField.Alignment.HarperRoughDecomposition
