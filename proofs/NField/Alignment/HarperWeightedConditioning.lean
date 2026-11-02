/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import NField.Alignment.HarperConditioningDecay

/-!
# Weighted conditioning without a lower bound on box weights

The finite functional is written as w^(1/4) v^(3/4), so zero weights
are allowed throughout. Holder and fractional subadditivity give both
accumulated comparison losses. The per-box error bounds and total moment
are explicit hypotheses here; this module does not construct the smooth
partition or prove its analytic character/random approximation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperWeightedConditioning

open scoped BigOperators

variable {ι : Type*}

def conditioningSum (s : Finset ι) (w v : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (w i)^(1/4 : ℝ) * (v i)^(3/4 : ℝ)

theorem weighted_holder (s : Finset ι) (w v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    conditioningSum s w v ≤ (∑ i ∈ s, w i)^(1/4 : ℝ) * (∑ i ∈ s, v i)^(3/4 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4/3) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => (w i)^(1/4 : ℝ)) (g := fun i => (v i)^(3/4 : ℝ)) hpq
    (fun i hi => Real.rpow_nonneg (hw i hi) _) (fun i hi => Real.rpow_nonneg (hv i hi) _)
  have hwp : (∑ i ∈ s, ((w i)^(1/4 : ℝ))^(4 : ℝ)) = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hw i hi)]
    norm_num
  have hvp : (∑ i ∈ s, ((v i)^(3/4 : ℝ))^(4/3 : ℝ)) = ∑ i ∈ s, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hv i hi)]
    norm_num
  simpa only [conditioningSum, hwp, hvp, show (1/(4/3) : ℝ)=3/4 by norm_num] using h

theorem conditional_term_identity {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    w * (v/w)^(3/4 : ℝ) = w^(1/4 : ℝ)*v^(3/4 : ℝ) := by
  rcases eq_or_lt_of_le hw with he | hp
  · subst w
    norm_num
  · rw [Real.div_rpow hv hp.le, div_eq_mul_inv]
    have he : w * (w^(3/4 : ℝ))⁻¹ = w^(1/4 : ℝ) := by
      calc
        _ = w^(1 : ℝ)*w^(-(3/4 : ℝ)) := by rw [Real.rpow_one, Real.rpow_neg hp.le]
        _ = _ := by rw [← Real.rpow_add hp]; norm_num
    calc
      w * (v^(3/4 : ℝ)*(w^(3/4 : ℝ))⁻¹) =
          (w*(w^(3/4 : ℝ))⁻¹)*v^(3/4 : ℝ) := by ring
      _ = _ := by rw [he]

theorem fourth_root_sum_bound (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, (w i)^(1/4 : ℝ)) ≤ (s.card : ℝ)^(3/4 : ℝ) := by
  have h := weighted_holder s w (fun _ => 1) hw (fun _ _ => by norm_num)
  simpa only [conditioningSum, Real.one_rpow, mul_one, hsum, one_mul,
    Finset.sum_const, nsmul_eq_mul] using h

theorem three_quarters_sum_bound (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) :
    (∑ i ∈ s, (v i)^(3/4 : ℝ)) ≤
      (s.card : ℝ)^(1/4 : ℝ) * (∑ i ∈ s, v i)^(3/4 : ℝ) := by
  have h := weighted_holder s (fun _ => 1) v (fun _ _ => by norm_num) hv
  simpa only [conditioningSum, Real.one_rpow, one_mul,
    Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem polynomial_error_bound (s : Finset ι) (w u v : ι → ℝ) {epsilon : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hsum : ∑ i ∈ s, w i = 1) (hepsilon : 0 ≤ epsilon)
    (herror : ∀ i ∈ s, u i ≤ v i + epsilon) :
    conditioningSum s w u ≤ conditioningSum s w v + ((s.card : ℝ)*epsilon)^(3/4 : ℝ) := by
  have hfrac (i : ι) (hi : i ∈ s) : (u i)^(3/4 : ℝ) ≤ (v i)^(3/4 : ℝ)+epsilon^(3/4 : ℝ) :=
    (Real.rpow_le_rpow (hu i hi) (herror i hi) (by norm_num)).trans
      (Real.rpow_add_le_add_rpow (hv i hi) hepsilon (by norm_num) (by norm_num))
  calc
    _ ≤ ∑ i ∈ s, (w i)^(1/4 : ℝ) * ((v i)^(3/4 : ℝ)+epsilon^(3/4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hfrac i hi) (Real.rpow_nonneg (hw i hi) _)
    _ = conditioningSum s w v + (∑ i ∈ s, (w i)^(1/4 : ℝ))*epsilon^(3/4 : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, conditioningSum]
    _ ≤ conditioningSum s w v + (s.card : ℝ)^(3/4 : ℝ)*epsilon^(3/4 : ℝ) := by
      gcongr
      exact fourth_root_sum_bound s w hw hsum
    _ = _ := by rw [Real.mul_rpow (Nat.cast_nonneg _) hepsilon]

theorem weight_error_bound (s : Finset ι) (w r v : ι → ℝ) {theta x : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, 0 ≤ r i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (htheta : 0 ≤ theta) (hmoment : ∑ i ∈ s, v i ≤ x)
    (herror : ∀ i ∈ s, w i ≤ r i + theta) :
    conditioningSum s w v ≤ conditioningSum s r v +
      x^(3/4 : ℝ)*((s.card : ℝ)*theta)^(1/4 : ℝ) := by
  have hfrac (i : ι) (hi : i ∈ s) : (w i)^(1/4 : ℝ) ≤ (r i)^(1/4 : ℝ)+theta^(1/4 : ℝ) :=
    (Real.rpow_le_rpow (hw i hi) (herror i hi) (by norm_num)).trans
      (Real.rpow_add_le_add_rpow (hr i hi) htheta (by norm_num) (by norm_num))
  have hsum := (three_quarters_sum_bound s v hv).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg hv) hmoment (by norm_num : (0 : ℝ) ≤ 3/4))
      (Real.rpow_nonneg (Nat.cast_nonneg s.card) (1/4 : ℝ)))
  calc
    _ ≤ ∑ i ∈ s, ((r i)^(1/4 : ℝ)+theta^(1/4 : ℝ)) * (v i)^(3/4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hfrac i hi) (Real.rpow_nonneg (hv i hi) _)
    _ = conditioningSum s r v + theta^(1/4 : ℝ)*(∑ i ∈ s, (v i)^(3/4 : ℝ)) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, conditioningSum]
    _ ≤ conditioningSum s r v + theta^(1/4 : ℝ)*
        ((s.card : ℝ)^(1/4 : ℝ)*x^(3/4 : ℝ)) := by
      gcongr
    _ = _ := by rw [Real.mul_rpow (Nat.cast_nonneg _) htheta]; ring

theorem transfer_from_box_errors (s : Finset ι) (w r u v : ι → ℝ) {x eta : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hsum : ∑ i ∈ s, w i = 1) (hx : 0 ≤ x) (heta : 0 ≤ eta)
    (hmoment : ∑ i ∈ s, v i ≤ x)
    (hpoly : ∀ i ∈ s, u i ≤ v i + x*eta)
    (hweight : ∀ i ∈ s, w i ≤ r i + eta) :
    conditioningSum s w u ≤ conditioningSum s r v +
      x^(3/4 : ℝ)*((s.card : ℝ)*eta)^(3/4 : ℝ) +
      x^(3/4 : ℝ)*((s.card : ℝ)*eta)^(1/4 : ℝ) := by
  have hp := polynomial_error_bound s w u v hw hu hv hsum (mul_nonneg hx heta) hpoly
  have hwgt := weight_error_bound s w r v hw hr hv heta hmoment hweight
  have he : ((s.card : ℝ)*(x*eta))^(3/4 : ℝ) =
      x^(3/4 : ℝ)*((s.card : ℝ)*eta)^(3/4 : ℝ) := by
    rw [show (s.card : ℝ)*(x*eta) = x*((s.card : ℝ)*eta) by ring,
      Real.mul_rpow hx (mul_nonneg (Nat.cast_nonneg _) heta)]
  rw [he] at hp
  linarith

open Filter HarperParameterBounds HarperRoundedCutoff HarperConditioningDecay

abbrev BoxIndex (x : ℝ) :=
  Fin (factorCount x) → Fin (2*rangeCount (cutoffLog x)+2)

/-- The printed two-loss transfer at the actual cutoff, with arbitrary
nonnegative constants in the two supplied per-box errors. The partition
and its error bounds are not constructed by this theorem. -/
theorem rounded_transfer_from_errors : ∀ᶠ x : ℝ in atTop,
    ∀ (w r u v : BoxIndex x → ℝ) (C D : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ r i) → (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
      (∑ i, w i) = 1 → 0 ≤ C → 0 ≤ D → (∑ i, v i) ≤ x →
      (∀ i, u i ≤ v i + C*x*boxError (cutoffLog x)) →
      (∀ i, w i ≤ r i + D*boxError (cutoffLog x)) →
      conditioningSum Finset.univ w u ≤ conditioningSum Finset.univ r v +
        C^(3/4 : ℝ)*polynomialLossScale x + D^(1/4 : ℝ)*weightLossScale x := by
  filter_upwards [eventually_ge_atTop (0 : ℝ), cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1]
    with x hx hell hlog
  dsimp only [Function.comp_apply] at hlog
  intro w r u v C D hw hr hu hv hsum hC hD hmoment hpoly hweight
  have hj : (0 : ℝ) < rangeCount (cutoffLog x) :=
    lt_of_lt_of_le zero_lt_one (rangeCount_bounds hell hlog).1
  have heta : 0 ≤ boxError (cutoffLog x) :=
    (Real.rpow_pos_of_pos (mul_pos hj hell) _).le
  have hB := (boxCount_pos (cutoffLog x)).le
  have hmass : 0 ≤ errorMass (cutoffLog x) := mul_nonneg hB heta
  have hcard : ((Finset.univ : Finset (BoxIndex x)).card : ℝ) = boxCount (cutoffLog x) := by
    simpa only [Finset.card_univ, BoxIndex] using box_count_cardinality x
  have hp := polynomial_error_bound Finset.univ w u v (fun i _ => hw i)
    (fun i _ => hu i) (fun i _ => hv i) hsum (mul_nonneg (mul_nonneg hC hx) heta)
    (fun i _ => hpoly i)
  have ht := weight_error_bound Finset.univ w r v (fun i _ => hw i)
    (fun i _ => hr i) (fun i _ => hv i) (mul_nonneg hD heta) hmoment
    (fun i _ => hweight i)
  rw [hcard] at hp ht
  have ep : (boxCount (cutoffLog x)*(C*x*boxError (cutoffLog x)))^(3/4 : ℝ) =
      C^(3/4 : ℝ)*polynomialLossScale x := by
    rw [show boxCount (cutoffLog x)*(C*x*boxError (cutoffLog x)) =
      C*(x*errorMass (cutoffLog x)) by unfold errorMass; ring,
      Real.mul_rpow hC (mul_nonneg hx hmass), Real.mul_rpow hx hmass]
    rfl
  have et : x^(3/4 : ℝ)*(boxCount (cutoffLog x)*(D*boxError (cutoffLog x)))^(1/4 : ℝ) =
      D^(1/4 : ℝ)*weightLossScale x := by
    rw [show boxCount (cutoffLog x)*(D*boxError (cutoffLog x)) =
      D*errorMass (cutoffLog x) by unfold errorMass; ring,
      Real.mul_rpow hD hmass]
    norm_num [weightLossScale, alpha]
    ring
  rw [ep] at hp
  rw [et] at ht
  linarith

end NField.Alignment.HarperWeightedConditioning
