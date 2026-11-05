/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFractionalConditioning
import NField.Alignment.HarperRetainedSum

/-!
# Actual retained random conditioning and the complete negligible error

The exact sum decomposition and finite fractional conditioning passage
combine with the actual character/random comparison. All errors are proved
negligible at the printed target, uniformly over bounded coefficients.
The estimate of the retained random conditioning sum remains separate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRetainedTransfer

open scoped BigOperators
open Filter Asymptotics HarperFractionalConditioning HarperRetainedSum
  HarperSmoothCount HarperSmoothCountDecay HarperSmoothRemoval
  HarperActualConditioning HarperWeightedConditioning HarperRoundedCutoff
  HarperConditioningDecay CollisionMertensInput SpectralRepulsion CollisionCharacterStructure

def removalLoss (C : ℝ) (p : ℕ) : ℝ :=
  2 * (smoothCount ((p : ℝ)-1) (smoothCutoff ((p : ℝ)-1)))^(3/4 : ℝ) +
    2 * transferLoss C p

theorem removalLoss_isLittleO (C : ℝ) :
    removalLoss C =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  (prime_square_smoothCount_decay.const_mul_left 2).add
    ((transferLoss_isLittleO C).const_mul_left 2)

def randomRetainedConditioning (p : ℕ) (c1 c2 : Coefficients p) (w : ℕ → ℂ) : ℝ :=
  conditioningSum Finset.univ (randomWeight p c1 c2)
    (randomMoment p c1 c2 (retainedCoefficient (smoothCutoff ((p : ℝ)-1)) w))

theorem random_conditioning_as_conditional {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (w : ℕ → ℂ) :
    randomRetainedConditioning p c1 c2 w =
      ∑ i, randomWeight p c1 c2 i *
        (randomMoment p c1 c2 (retainedCoefficient (smoothCutoff ((p : ℝ)-1)) w) i /
          randomWeight p c1 c2 i)^(3/4 : ℝ) := by
  unfold randomRetainedConditioning conditioningSum
  apply Finset.sum_congr rfl
  intro i _
  exact (conditional_term_identity (randomWeight_nonneg hell c1 c2 i)
    (randomMoment_nonneg hell c1 c2 _ i)).symm

theorem eventual_retained_transfer : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p^2)], p.Prime → ∀ (c1 c2 : Coefficients p) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c2 i r‖ ≤ 1) →
    (∀ n ∈ Finset.Icc 1 (p-1), ‖w n‖ ≤ 1) →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2 * randomRetainedConditioning p c1 c2 w + removalLoss C p := by
  obtain ⟨C, hC, ht⟩ := eventual_fractional_transfer
  refine ⟨C, hC, ht.mono ?_⟩
  intro p hp _ hprime c1 c2 w h1 h2 hw
  have hr := hp hprime c1 c2 (retainedCoefficient (smoothCutoff ((p : ℝ)-1)) w) h1 h2
    (fun n hn => (retainedCoefficient_norm_le _ w n).trans (hw n hn))
  have hs := short_moment_removal hprime (smoothCutoff ((p : ℝ)-1)) w hw
  dsimp only [randomRetainedConditioning, removalLoss]
  linarith

theorem eventual_retained_transfer_negligible {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p^2)], p.Prime → ∀ (c1 c2 : Coefficients p) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c2 i r‖ ≤ 1) →
    (∀ n ∈ Finset.Icc 1 (p-1), ‖w n‖ ≤ 1) →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2 * randomRetainedConditioning p c1 c2 w + epsilon * targetScale ((p : ℝ)-1) := by
  obtain ⟨C, _, ht⟩ := eventual_retained_transfer
  filter_upwards [ht, (removalLoss_isLittleO C).bound he,
    base_minus_one_tendsto.eventually_gt_atTop 0,
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hp hb hx hu
  dsimp only [Function.comp_apply] at hx hu
  have htarget : 0 ≤ targetScale ((p : ℝ)-1) := by unfold targetScale; positivity
  rw [Real.norm_of_nonneg htarget] at hb
  have herror : removalLoss C p ≤ epsilon * targetScale ((p : ℝ)-1) :=
    (le_abs_self _).trans hb
  intro _ hprime c1 c2 w h1 h2 hw
  have h := hp hprime c1 c2 w h1 h2 hw
  linarith

end NField.Alignment.HarperRetainedTransfer
