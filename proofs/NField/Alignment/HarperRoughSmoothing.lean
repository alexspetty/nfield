/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothingMoment
import NField.Alignment.HarperRoughDecomposition


/-!
# Smoothing the actual rough-factor sum

The original rough support is enlarged only by replacing its large-prime
condition with m > y. The positive rough factors retain their full finite
range and prime restrictions. Smoothing yields an explicit main average
and remainder, whose total expectation is bounded by the literal finite
sum of 1 + x/(m*X). The constructed box weights preserve this inequality;
their sum removes the conditioning exactly, including zero-weight cells.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRoughSmoothing

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperSmoothIntervals HarperSmoothingMoment
  HarperRoughSupport HarperSmoothRough HarperRoughDecomposition HarperActualConditioning
  HarperProductApproximation HarperRoundedCutoff HarperWeightedConditioning
  HarperConditioningFrequencies HarperParameterBounds

def roughAverageSupport (N : ℕ) (P y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun m : ℕ => y < (m : ℝ) ∧ m.Coprime (primeBase P))

theorem roughAverageSupport_mem {N m : ℕ} {P y : ℝ} :
    m ∈ roughAverageSupport N P y ↔
      0 < m ∧ m ≤ N ∧ y < (m : ℝ) ∧ ∀ r : ℕ, r.Prime → r ∣ m → P < (r : ℝ) := by
  simp only [roughAverageSupport, Finset.mem_filter, Finset.mem_Icc, rough_coprime_iff]
  constructor
  · rintro ⟨⟨hm, hN⟩, hy, hp⟩
    exact ⟨hm, hN, hy, hp⟩
  · rintro ⟨hm, hN, hy, hp⟩
    exact ⟨⟨hm, hN⟩, hy, hp⟩

theorem roughSupport_subset_average (N : ℕ) (P y : ℝ) :
    roughSupport N P y ⊆ roughAverageSupport N P y := by
  intro m hm
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1,
    roughSupport_gt_y hm, (Finset.mem_filter.mp hm).2⟩

private theorem averageSupport_pos {N m : ℕ} {P y : ℝ}
    (hm : m ∈ roughAverageSupport N P y) : (0 : ℝ) < m := by
  exact_mod_cast (roughAverageSupport_mem.mp hm).1

def smoothRoughAverage (x P y X : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) : ℝ :=
  ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
    smoothAverage x P (m : ℝ) X (fun n => w (m*n) * steinhaus n ω)

def roughTailAverage (x P y X : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) : ℝ :=
  ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
    tailAverage x P (m : ℝ) X (fun n => w (m*n) * steinhaus n ω)

def roughSmoothingError (x P y X : ℝ) : ℝ :=
  ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, (1+x/((m : ℝ)*X))

theorem smoothRoughAverage_nonneg {X : ℝ} (hX : 0 < X)
    (x P y : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) : 0 ≤ smoothRoughAverage x P y X w ω :=
  Finset.sum_nonneg (fun _ hm => smoothAverage_nonneg (averageSupport_pos hm) hX _ _ _)

theorem roughTailAverage_nonneg {X : ℝ} (hX : 0 < X)
    (x P y : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) : 0 ≤ roughTailAverage x P y X w ω :=
  Finset.sum_nonneg (fun _ hm => tailAverage_nonneg (averageSupport_pos hm) hX _ _ _)

theorem smoothRoughAverage_integrable {x X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (P y : ℝ) (w : ℕ → ℂ) : Integrable (smoothRoughAverage x P y X w) phaseMeasure :=
  integrable_finsetSum _ (fun _ hm => smoothAverage_integrable hx (averageSupport_pos hm) hX _)

theorem roughTailAverage_integrable {X : ℝ} (hX : 0 < X)
    (x P y : ℝ) (w : ℕ → ℂ) : Integrable (roughTailAverage x P y X w) phaseMeasure :=
  integrable_finsetSum _ (fun _ hm => tailAverage_integrable (averageSupport_pos hm) hX _ _ _)

theorem roughSquare_le_smoothing {x X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (P y : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) :
    roughSquare x P y w ω ≤ 2*smoothRoughAverage x P y X w ω +
      2*roughTailAverage x P y X w ω := by
  calc
    _ ≤ ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
        ‖smoothSum (x/(m : ℝ)) P (fun n => w (m*n)*steinhaus n ω)‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (roughSupport_subset_average _ _ _)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
        (2*smoothAverage x P (m : ℝ) X (fun n => w (m*n)*steinhaus n ω) +
         2*tailAverage x P (m : ℝ) X (fun n => w (m*n)*steinhaus n ω)) :=
      Finset.sum_le_sum (fun m hm => smoothSum_smoothing hx (averageSupport_pos hm) hX _)
    _ = _ := by simp only [smoothRoughAverage, roughTailAverage, Finset.sum_add_distrib,
      Finset.mul_sum]

theorem roughTailAverage_expectation_bound {x X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (P y : ℝ) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) :
    (∫ ω, roughTailAverage x P y X w ω ∂phaseMeasure) ≤ roughSmoothingError x P y X := by
  unfold roughTailAverage
  rw [integral_finsetSum _ (fun _ hm =>
    tailAverage_integrable (averageSupport_pos hm) hX _ _ _)]
  exact Finset.sum_le_sum (fun _ hm => tailAverage_expectation_bound hx
    (averageSupport_pos hm) hX _ (fun n _ => hw _))

def boxMoment (p : ℕ) (c1 c2 : Coefficients p) (i : Boxes p)
    (F : PhaseSpace → ℝ) : ℝ :=
  ∫ ω, F ω * smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure

private theorem box_measurable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) :
    Measurable (fun ω => smoothBox p c1 c2 i (fun n => steinhaus n ω)) :=
  random_smooth_measurable (precision_pos hell) _ _ _ _ _ _

private theorem box_norm_le_one {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (ω : PhaseSpace) :
    ‖smoothBox p c1 c2 i (fun n => steinhaus n ω)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothBox_nonneg hell c1 c2 i _)]
  exact smoothValue_le_one (precision_pos hell) _ _ _ _ _ _ _

theorem boxMoment_integrable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) {F : PhaseSpace → ℝ}
    (hF : Integrable F phaseMeasure) :
    Integrable (fun ω => F ω * smoothBox p c1 c2 i (fun n => steinhaus n ω)) phaseMeasure :=
  hF.mul_bdd (box_measurable hell c1 c2 i).aestronglyMeasurable
    (Filter.Eventually.of_forall (box_norm_le_one hell c1 c2 i))

theorem boxMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) {F : PhaseSpace → ℝ}
    (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ boxMoment p c1 c2 i F :=
  integral_nonneg (fun ω => mul_nonneg (hF ω) (smoothBox_nonneg hell c1 c2 i _))

theorem boxMoment_sum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {F : PhaseSpace → ℝ} (hF : Integrable F phaseMeasure) :
    ∑ i, boxMoment p c1 c2 i F = ∫ ω, F ω ∂phaseMeasure := by
  unfold boxMoment
  rw [← integral_finsetSum _ (fun i _ => boxMoment_integrable hell c1 c2 i hF)]
  simp_rw [← Finset.mul_sum, smoothBox_sum, mul_one]

theorem randomWeight_sum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) : ∑ i, randomWeight p c1 c2 i = 1 := by
  simpa only [boxMoment, one_mul, integral_const, probReal_univ, one_smul,
    randomWeight] using boxMoment_sum hell c1 c2 (integrable_const (1 : ℝ))

theorem weighted_rough_smoothing {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) {x X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (P y : ℝ) (w : ℕ → ℂ) :
    boxMoment p c1 c2 i (roughSquare x P y w) ≤
      2*boxMoment p c1 c2 i (smoothRoughAverage x P y X w) +
      2*boxMoment p c1 c2 i (roughTailAverage x P y X w) := by
  have hA := boxMoment_integrable hell c1 c2 i (smoothRoughAverage_integrable hx hX P y w)
  have hB := boxMoment_integrable hell c1 c2 i (roughTailAverage_integrable hX x P y w)
  unfold boxMoment
  calc
    _ ≤ ∫ ω, 2*(smoothRoughAverage x P y X w ω * smoothBox p c1 c2 i (fun n => steinhaus n ω)) +
        2*(roughTailAverage x P y X w ω * smoothBox p c1 c2 i (fun n => steinhaus n ω))
        ∂phaseMeasure := by
      apply integral_mono (weighted_roughSquare_integrable hell c1 c2 i x P y w)
        ((hA.const_mul 2).add (hB.const_mul 2))
      intro ω
      have h := mul_le_mul_of_nonneg_right (roughSquare_le_smoothing hx hX P y w ω)
        (smoothBox_nonneg hell c1 c2 i (fun n => steinhaus n ω))
      simpa only [add_mul, mul_assoc, Pi.add_apply] using h
    _ = _ := by rw [integral_add (hA.const_mul 2) (hB.const_mul 2),
      integral_const_mul, integral_const_mul]

end NField.Alignment.HarperRoughSmoothing
