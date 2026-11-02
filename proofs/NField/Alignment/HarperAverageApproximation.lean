/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperProductApproximation

/-!
# Averaged approximation of a full conditioning box

Every nonempty subset of actual Taylor errors is included. The averaged
error is bounded by an explicit binomial sum, for both the short-sum-weighted
comparison and the unweighted partition weights. No asymptotic estimate for
that binomial sum is assumed or asserted here.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperAverageApproximation

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperPrimeProductMoment HarperRemainderProduct
  HarperProductApproximation HarperPrimeTaylorComparison SpectralRepulsion
  CollisionMertensInput CollisionCharacterStructure

theorem integral_box_approximation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {delta : ℝ} (hd : 0 < delta) (J S A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ)
    (z : Ω → ℕ → ℂ) (W : Ω → ℝ) (hW : ∀ ω, 0 ≤ W ω) (C : Finset (Fin A) → ℝ)
    (hG : Integrable (fun ω => W ω * smoothValue delta J A P labels c1 c2 (z ω)) μ)
    (hT : Integrable (fun ω => W ω * taylorValue delta J (2 * S) A P labels c1 c2 (z ω)) μ)
    (hR : ∀ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
      Integrable (fun ω => W ω * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (z ω)) μ)
    (hC : ∀ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
      (∫ ω, W ω * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (z ω) ∂μ) ≤ C t) :
    |(∫ ω, W ω * smoothValue delta J A P labels c1 c2 (z ω) ∂μ) -
      ∫ ω, W ω * taylorValue delta J (2 * S) A P labels c1 c2 (z ω) ∂μ| ≤
      ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅, C t := by
  rw [← integral_sub hG hT]
  calc
    _ ≤ ∫ ω, |W ω * smoothValue delta J A P labels c1 c2 (z ω) -
        W ω * taylorValue delta J (2 * S) A P labels c1 c2 (z ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => W ω * smoothValue delta J A P labels c1 c2 (z ω) -
          W ω * taylorValue delta J (2 * S) A P labels c1 c2 (z ω))
    _ ≤ ∫ ω, ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        W ω * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (z ω) ∂μ :=
      integral_mono (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hG.sub hT).norm)
        (integrable_finsetSum _ hR) (fun ω => weighted_product_error hd J S A P labels c1 c2 (z ω) (hW ω))
    _ = ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        ∫ ω, W ω * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (z ω) ∂μ :=
      integral_finsetSum _ hR
    _ ≤ _ := Finset.sum_le_sum hC

theorem average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω)) (by positivity)

theorem average_abs_difference {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    |uniformAverage f - uniformAverage g| ≤ uniformAverage (fun ω => |f ω - g ω|) := by
  unfold uniformAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem average_box_approximation {Ω : Type*} [Fintype Ω]
    {delta : ℝ} (hd : 0 < delta) (J S A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ)
    (z : Ω → ℕ → ℂ) (W : Ω → ℝ) (hW : ∀ ω, 0 ≤ W ω) (C : Finset (Fin A) → ℝ)
    (hC : ∀ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
      uniformAverage (fun ω => W ω * ∏ i ∈ t,
        remainder delta J S P (labels i) (c1 i) (c2 i) (z ω)) ≤ C t) :
    |uniformAverage (fun ω => W ω * smoothValue delta J A P labels c1 c2 (z ω)) -
      uniformAverage (fun ω => W ω * taylorValue delta J (2 * S) A P labels c1 c2 (z ω))| ≤
      ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅, C t := by
  calc
    _ ≤ _ := average_abs_difference _ _
    _ ≤ uniformAverage (fun ω => ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        W ω * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (z ω)) :=
      average_mono (fun ω => weighted_product_error hd J S A P labels c1 c2 (z ω) (hW ω))
    _ = _ := uniformAverage_finset_sum _ _
    _ ≤ _ := Finset.sum_le_sum hC

theorem random_weighted_approximation_bound {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (A : ℕ) (P : ℝ) (s : Finset ℕ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≠ 0) {B : ℝ} (hB : ∀ i, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    |(∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
        smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure) -
      ∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
        taylorValue delta J (2 * S) A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      shortEnergy P s w * errorSum delta J S A B := by
  calc
    _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        shortEnergy P s w * productBound delta J S t.card B := by
      apply integral_box_approximation hd J S A P labels c1 c2 (fun ω n => steinhaus n ω)
        (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2) (fun _ => sq_nonneg _)
        (fun t => shortEnergy P s w * productBound delta J S t.card B)
      · exact random_weighted_smooth_integrable hd J A P s labels c1 c2 w
      · simpa only [mul_comm] using weighted_taylor_integrable delta J (2 * S) A P labels c1 c2 s w
      · intro t ht
        exact random_weighted_remainder_integrable t
          (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1) hd hJ hS P s labels c1 c2 w
      · intro t ht
        exact random_weighted_remainder_bound t
          (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1)
          hd hJ hS P s labels c1 c2 w hs (fun i _ => hB i)
    _ = _ := by rw [← Finset.mul_sum, ← errorSum_eq_subsets]

theorem character_weighted_approximation_bound {q : ℕ} [NeZero q]
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (A : ℕ) (P x : ℝ) (s : Finset ℕ) (labels : Fin A → Fin (2 * J + 2))
    (c1 c2 : Fin A → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q)
    (hsize : ∀ j ≤ A, x * (P ^ 2) ^ (S * j) < q)
    {B : ℝ} (hB : ∀ i, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    |uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
        smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod q))) -
      uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
        taylorValue delta J (2 * S) A P labels c1 c2 (fun n => χ (n : ZMod q)))| ≤
      shortEnergy P s w * errorSum delta J S A B := by
  calc
    _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        shortEnergy P s w * productBound delta J S t.card B := by
      apply average_box_approximation hd J S A P labels c1 c2 (fun (χ : Character q) n => χ (n : ZMod q))
        (fun χ => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2) (fun _ => sq_nonneg _)
        (fun t => shortEnergy P s w * productBound delta J S t.card B)
      intro t ht
      exact character_weighted_remainder_bound t
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1) hd hJ hS P x s labels c1 c2 w
        hs ha (hsize t.card (by simpa using Finset.card_le_univ t)) (fun i _ => hB i)
    _ = _ := by rw [← Finset.mul_sum, ← errorSum_eq_subsets]

theorem random_approximation_bound {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (A : ℕ) (P : ℝ) (labels : Fin A → Fin (2 * J + 2))
    (c1 c2 : Fin A → ℕ → ℂ) {B : ℝ} (hB : ∀ i, primeEnergy P (c1 i) (c2 i) ≤ B) :
    |(∫ ω, smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure) -
      ∫ ω, taylorValue delta J (2 * S) A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      errorSum delta J S A B := by
  rw [errorSum_eq_subsets]
  have h := integral_box_approximation (μ := phaseMeasure) hd J S A P labels c1 c2
    (fun ω n => steinhaus n ω) (fun _ => 1) (fun _ => by norm_num)
    (fun t => productBound delta J S t.card B)
    (by simpa using random_weighted_smooth_integrable hd J A P {1} labels c1 c2 (fun _ => 1))
    (by simpa using weighted_taylor_integrable delta J (2 * S) A P labels c1 c2 {1} (fun _ => 1))
    (fun t ht => by
      simpa only [one_mul] using random_remainder_integrable t
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1) hd hJ hS P labels c1 c2)
    (fun t ht => by
      simpa only [one_mul] using random_remainder_bound t
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1) hd hJ hS P labels c1 c2 (fun i _ => hB i))
  simpa only [one_mul] using h

theorem character_approximation_bound {q : ℕ} [NeZero q]
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (A : ℕ) (P : ℝ) (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : ∀ j ≤ A, (P ^ 2) ^ (S * j) < q)
    {B : ℝ} (hB : ∀ i, primeEnergy P (c1 i) (c2 i) ≤ B) :
    |uniformAverage (fun χ : Character q => smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod q))) -
      uniformAverage (fun χ : Character q => taylorValue delta J (2 * S) A P labels c1 c2 (fun n => χ (n : ZMod q)))| ≤
      errorSum delta J S A B := by
  rw [errorSum_eq_subsets]
  have h := average_box_approximation hd J S A P labels c1 c2
    (fun (χ : Character q) n => χ (n : ZMod q)) (fun _ => 1) (fun _ => by norm_num)
    (fun t => productBound delta J S t.card B)
    (fun t ht => by
      simpa only [one_mul] using character_remainder_bound t
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1) hd hJ hS P labels c1 c2
        ha (hsize t.card (by simpa using Finset.card_le_univ t)) (fun i _ => hB i))
  simpa only [one_mul] using h

end NField.Alignment.HarperAverageApproximation
