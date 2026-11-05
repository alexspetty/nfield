/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperActualConditioning

/-!
# From the actual fractional moment to random conditioning

Finite weighted Holder proves the fractional conditioning inequality without
dividing by a box weight. The constructed partition and previously proved
actual comparison then transfer the short three-halves moment to the random
conditioning sum, with the complete negligible error retained.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFractionalConditioning

open scoped BigOperators
open HarperWeightedConditioning HarperActualConditioning MagnitudeShortComparison
  SpectralRepulsion CollisionCharacterStructure HarperRoundedCutoff
  HarperConditioningDecay CollisionMertensInput

theorem weighted_fractional_bound {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    uniformAverage (fun x => (f x)^(3/2 : ℝ) * g x) ≤
      (uniformAverage g)^(1/4 : ℝ) *
        (uniformAverage (fun x => (f x)^2 * g x))^(3/4 : ℝ) := by
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ = conditioningSum Finset.univ (fun x => c*g x) (fun x => c*((f x)^2*g x)) := by
      unfold uniformAverage conditioningSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hcg : 0 ≤ c*g x := mul_nonneg hc (hg x)
      change c*((f x)^(3/2 : ℝ)*g x) = _
      dsimp only
      rw [show c*((f x)^2*g x) = (c*g x)*(f x)^2 by ring,
        Real.mul_rpow hcg (sq_nonneg _)]
      simp only [← mul_assoc]
      rw [← Real.rpow_add' hcg (by norm_num), ← Real.rpow_natCast_mul (hf x)]
      norm_num
      ring
    _ ≤ (∑ x, c*g x)^(1/4 : ℝ) * (∑ x, c*((f x)^2*g x))^(3/4 : ℝ) :=
      weighted_holder Finset.univ _ _ (fun x _ => mul_nonneg hc (hg x))
        (fun x _ => mul_nonneg hc (mul_nonneg (sq_nonneg _) (hg x)))
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; rfl

theorem fractional_conditioning_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ i x, 0 ≤ g i x) (hsum : ∀ x, ∑ i, g i x = 1) :
    uniformAverage (fun x => (f x)^(3/2 : ℝ)) ≤
      conditioningSum Finset.univ (fun i => uniformAverage (g i))
        (fun i => uniformAverage (fun x => (f x)^2*g i x)) := by
  calc
    _ = ∑ i, uniformAverage (fun x => (f x)^(3/2 : ℝ)*g i x) := by
      rw [← uniformAverage_sum]
      simp_rw [← Finset.mul_sum, hsum, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => weighted_fractional_bound f (g i) hf (hg i))

theorem character_fractional_conditioning {p : ℕ} [NeZero (p^2)]
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (w : ℕ → ℂ) :
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      conditioningSum Finset.univ (characterWeight p c1 c2) (characterMoment p c1 c2 w) := by
  exact fractional_conditioning_bound _ _ (fun _ => norm_nonneg _)
    (fun i χ => smoothBox_nonneg hell c1 c2 i _) (fun χ => smoothBox_sum p c1 c2 _)

def transferLoss (C : ℝ) (p : ℕ) : ℝ :=
  C^(3/4 : ℝ) * polynomialLossScale ((p : ℝ)-1) +
    (2 : ℝ)^(1/4 : ℝ) * weightLossScale ((p : ℝ)-1)

open Filter Asymptotics

theorem transferLoss_isLittleO (C : ℝ) :
    transferLoss C =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  actual_loss_decay C

theorem eventual_fractional_transfer : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p^2)], p.Prime → ∀ (c1 c2 : Coefficients p) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)) → ‖c2 i r‖ ≤ 1) →
    (∀ n ∈ Finset.Icc 1 (p-1), ‖w n‖ ≤ 1) →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      conditioningSum Finset.univ (randomWeight p c1 c2) (randomMoment p c1 c2 w) +
        transferLoss C p := by
  obtain ⟨C, hC, ht⟩ := eventual_actual_transfer
  refine ⟨C, hC, ?_⟩
  filter_upwards [ht, (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hp hell
  dsimp only [Function.comp_apply] at hell
  intro _ hprime c1 c2 w h1 h2 hw
  exact (character_fractional_conditioning hell c1 c2 w).trans
    (by simpa only [transferLoss, add_assoc] using hp hprime c1 c2 w h1 h2 hw)

end NField.Alignment.HarperFractionalConditioning
