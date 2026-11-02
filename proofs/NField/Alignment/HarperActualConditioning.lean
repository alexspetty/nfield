/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperBoxComparison
import NField.Alignment.HarperWeightedConditioning

/-!
# Conditioning with the actual character and random box averages

The weights, second moments and their totals are constructed here. The
per-box comparison estimates discharge the analytic hypotheses of the
finite conditioning inequality, including boxes of zero weight.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperActualConditioning

open scoped BigOperators
open MeasureTheory Filter Asymptotics SteinhausMoment HarperProductApproximation
  HarperBoxComparison HarperParameterBounds HarperRoundedCutoff HarperConditioningDecay
  HarperWeightedConditioning HarperPartition MagnitudeShortComparison
  SpectralRepulsion CollisionMertensInput CollisionCharacterStructure

abbrev Coefficients (p : ℕ) := Fin (factorCount ((p : ℝ) - 1)) → ℕ → ℂ
abbrev Boxes (p : ℕ) := BoxIndex ((p : ℝ) - 1)

def smoothBox (p : ℕ) (c1 c2 : Coefficients p) (i : Boxes p) (z : ℕ → ℂ) : ℝ :=
  smoothValue (precision (cutoffLog ((p : ℝ) - 1)))
    (rangeCount (cutoffLog ((p : ℝ) - 1))) (factorCount ((p : ℝ) - 1))
    (primeCutoff ((p : ℝ) - 1)) i c1 c2 z

def characterWeight (p : ℕ) [NeZero (p ^ 2)] (c1 c2 : Coefficients p) (i : Boxes p) : ℝ :=
  uniformAverage (fun χ : Character (p ^ 2) => smoothBox p c1 c2 i (fun n => χ (n : ZMod (p ^ 2))))

def randomWeight (p : ℕ) (c1 c2 : Coefficients p) (i : Boxes p) : ℝ :=
  ∫ ω, smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure

def characterMoment (p : ℕ) [NeZero (p ^ 2)] (c1 c2 : Coefficients p)
    (w : ℕ → ℂ) (i : Boxes p) : ℝ :=
  uniformAverage (fun χ : Character (p ^ 2) =>
    ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * χ (n : ZMod (p ^ 2))‖ ^ 2 *
      smoothBox p c1 c2 i (fun n => χ (n : ZMod (p ^ 2))))

def randomMoment (p : ℕ) (c1 c2 : Coefficients p) (w : ℕ → ℂ) (i : Boxes p) : ℝ :=
  ∫ ω, ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * steinhaus n ω‖ ^ 2 *
    smoothBox p c1 c2 i (fun n => steinhaus n ω) ∂phaseMeasure

theorem smoothBox_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ) - 1))
    (c1 c2 : Coefficients p) (i : Boxes p) (z : ℕ → ℂ) : 0 ≤ smoothBox p c1 c2 i z :=
  smoothValue_nonneg (precision_pos hell) _ _ _ _ _ _ _

theorem smoothBox_sum (p : ℕ) (c1 c2 : Coefficients p) (z : ℕ → ℂ) :
    ∑ i, smoothBox p c1 c2 i z = 1 := boxWeight_sum _ _ _

theorem characterWeight_nonneg {p : ℕ} [NeZero (p ^ 2)]
    (hell : 0 < cutoffLog ((p : ℝ) - 1)) (c1 c2 : Coefficients p) (i : Boxes p) :
    0 ≤ characterWeight p c1 c2 i := by
  unfold characterWeight uniformAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => smoothBox_nonneg hell c1 c2 i _))

theorem randomWeight_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ) - 1))
    (c1 c2 : Coefficients p) (i : Boxes p) : 0 ≤ randomWeight p c1 c2 i :=
  integral_nonneg (fun _ => smoothBox_nonneg hell c1 c2 i _)

theorem characterMoment_nonneg {p : ℕ} [NeZero (p ^ 2)]
    (hell : 0 < cutoffLog ((p : ℝ) - 1)) (c1 c2 : Coefficients p) (w : ℕ → ℂ) (i : Boxes p) :
    0 ≤ characterMoment p c1 c2 w i := by
  unfold characterMoment uniformAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (sq_nonneg _) (smoothBox_nonneg hell c1 c2 i _)))

theorem randomMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ) - 1))
    (c1 c2 : Coefficients p) (w : ℕ → ℂ) (i : Boxes p) : 0 ≤ randomMoment p c1 c2 w i :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (smoothBox_nonneg hell c1 c2 i _))

theorem characterWeight_sum (p : ℕ) [NeZero (p ^ 2)] (c1 c2 : Coefficients p) :
    ∑ i, characterWeight p c1 c2 i = 1 := by
  unfold characterWeight
  rw [← uniformAverage_sum]
  simp only [smoothBox_sum, uniformAverage_one]

theorem randomMoment_total {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ) - 1))
    (c1 c2 : Coefficients p) (w : ℕ → ℂ) :
    ∑ i, randomMoment p c1 c2 w i = ∑ n ∈ Finset.Icc 1 (p - 1), ‖w n‖ ^ 2 := by
  have hi (i : Boxes p) : Integrable (fun ω =>
      ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * steinhaus n ω‖ ^ 2 *
        smoothBox p c1 c2 i (fun n => steinhaus n ω)) phaseMeasure :=
    random_weighted_smooth_integrable (precision_pos hell) _ _ _ _ i c1 c2 w
  unfold randomMoment
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [← Finset.mul_sum, smoothBox_sum, mul_one]
  exact polynomial_second_moment _ _ (fun n hn => by have := (Finset.mem_Icc.mp hn).1; omega)

theorem randomMoment_total_le {p : ℕ} (hp : 1 ≤ p)
    (hell : 0 < cutoffLog ((p : ℝ) - 1)) (c1 c2 : Coefficients p) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Icc 1 (p - 1), ‖w n‖ ≤ 1) :
    ∑ i, randomMoment p c1 c2 w i ≤ (p : ℝ) - 1 := by
  rw [randomMoment_total hell]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (p - 1), (1 : ℝ) :=
      Finset.sum_le_sum (fun n hn => pow_le_one₀ (norm_nonneg _) (hw n hn))
    _ = _ := by simp [Nat.cast_sub hp]

/-- The two printed accumulated losses for actual averages, with a positive
absolute constant and all per-box error and moment hypotheses discharged. -/
theorem eventual_actual_transfer : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p ^ 2)], p.Prime → ∀ (c1 c2 : Coefficients p) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ) - 1)) → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ) - 1)) → ‖c2 i r‖ ≤ 1) →
    (∀ n ∈ Finset.Icc 1 (p - 1), ‖w n‖ ≤ 1) →
    conditioningSum Finset.univ (characterWeight p c1 c2) (characterMoment p c1 c2 w) ≤
      conditioningSum Finset.univ (randomWeight p c1 c2) (randomMoment p c1 c2 w) +
        C ^ (3/4 : ℝ) * polynomialLossScale ((p : ℝ) - 1) +
        (2 : ℝ) ^ (1/4 : ℝ) * weightLossScale ((p : ℝ) - 1) := by
  obtain ⟨C, hC, hpoly⟩ := eventual_weighted_box_error
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpoly, eventual_weight_box_error,
    base_minus_one_tendsto.eventually rounded_transfer_from_errors,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hpbox hwbox ht hell
  dsimp only [Function.comp_apply] at hell
  dsimp only at hpbox hwbox ht
  intro _ hp c1 c2 w h1 h2 hw
  apply ht (characterWeight p c1 c2) (randomWeight p c1 c2)
    (characterMoment p c1 c2 w) (randomMoment p c1 c2 w) C 2
    (characterWeight_nonneg hell c1 c2) (randomWeight_nonneg hell c1 c2)
    (characterMoment_nonneg hell c1 c2 w) (randomMoment_nonneg hell c1 c2 w)
    (characterWeight_sum p c1 c2) hC.le (by norm_num)
    (randomMoment_total_le hp.one_lt.le hell c1 c2 w hw)
  · intro i
    have h := (abs_le.mp (hpbox hp i c1 c2 w h1 h2 hw)).2
    change characterMoment p c1 c2 w i - randomMoment p c1 c2 w i ≤ _ at h
    linarith
  · intro i
    have h := (abs_le.mp (hwbox hp i c1 c2 h1 h2)).2
    change characterWeight p c1 c2 i - randomWeight p c1 c2 i ≤ _ at h
    linarith

theorem actual_loss_decay (C : ℝ) :
    (fun p : ℕ => C ^ (3/4 : ℝ) * polynomialLossScale ((p : ℝ) - 1) +
      (2 : ℝ) ^ (1/4 : ℝ) * weightLossScale ((p : ℝ) - 1)) =o[atTop]
        (fun p : ℕ => targetScale ((p : ℝ) - 1)) :=
  (prime_square_loss_scales_decay.1.const_mul_left _).add
    (prime_square_loss_scales_decay.2.const_mul_left _)

end NField.Alignment.HarperActualConditioning
