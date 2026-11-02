/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeProductMoment

/-!
# Products of actual partition Taylor remainders

Every partition label, including the outside cell, has the same explicit
remainder majorant. The factorial moment estimates bound every nonempty
subset product, with the full factorials and prime energy retained.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRemainderProduct

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperPrimeEvenMoment HarperPrimeProductMoment
  HarperPartition HarperPartitionDerivative HarperPartitionTaylor
  HarperPrimeTaylorComparison CollisionMertensInput CollisionCharacterStructure SpectralRepulsion

def remainderScale (delta : ℝ) (J S : ℕ) : ℝ :=
  (3 * (J : ℝ) / (delta * (S : ℝ) * ((2 * S).factorial : ℝ))) * (2 * Real.pi / delta) ^ (2 * S)

def remainder (delta : ℝ) (J S : ℕ) (P : ℝ) (i : Fin (2 * J + 2))
    (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : ℝ :=
  |labelWeight delta J i (primeArgument P c1 c2 z) -
    (polynomial delta J i (2 * S)).eval (primeArgument P c1 c2 z)|

def majorant (delta : ℝ) (J S : ℕ) (P : ℝ) (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : ℝ :=
  remainderScale delta J S * ‖primePolynomial P c1 c2 z‖ ^ (2 * S)

def productBound (delta : ℝ) (J S j : ℕ) (B : ℝ) : ℝ :=
  remainderScale delta J S ^ j * ((S * j).factorial : ℝ) * B ^ (S * j)

theorem remainderScale_nonneg {delta : ℝ} (hd : 0 < delta) (J S : ℕ) :
    0 ≤ remainderScale delta J S := by unfold remainderScale; positivity

theorem majorant_nonneg {delta : ℝ} (hd : 0 < delta) (J S : ℕ) (P : ℝ)
    (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : 0 ≤ majorant delta J S P c1 c2 z :=
  mul_nonneg (remainderScale_nonneg hd J S) (by positivity)

theorem remainder_nonneg (delta : ℝ) (J S : ℕ) (P : ℝ) (i : Fin (2 * J + 2))
    (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : 0 ≤ remainder delta J S P i c1 c2 z := abs_nonneg _

/-- The literal Taylor error is bounded by the prime-polynomial norm majorant. -/
theorem remainder_le_majorant {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (P : ℝ) (i : Fin (2 * J + 2))
    (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) :
    remainder delta J S P i c1 c2 z ≤ majorant delta J S P c1 c2 z := by
  have he : |2 * Real.pi * primeArgument P c1 c2 z / delta| ^ (2 * S) =
      (2 * Real.pi / delta) ^ (2 * S) * |primeArgument P c1 c2 z| ^ (2 * S) := by
    rw [← mul_pow, ← abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi / delta), ← abs_mul]
    congr 2
    ring
  calc
    _ ≤ 3 * (J : ℝ) * |2 * Real.pi * primeArgument P c1 c2 z / delta| ^ (2 * S) /
        (delta * (S : ℝ) * ((2 * S).factorial : ℝ)) :=
      polynomial_even_remainder hd hJ hS i _
    _ = remainderScale delta J S * |primeArgument P c1 c2 z| ^ (2 * S) := by
      rw [he, remainderScale]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (primePolynomial P c1 c2 z)) _)
      (remainderScale_nonneg hd J S)

theorem random_remainder_measurable {delta : ℝ} (hd : 0 < delta) (J S : ℕ) (P : ℝ)
    (i : Fin (2 * J + 2)) (c1 c2 : ℕ → ℂ) :
    Measurable (fun ω => remainder delta J S P i c1 c2 (fun n => steinhaus n ω)) := by
  have ha : Measurable (fun ω => primeArgument P c1 c2 (fun n => steinhaus n ω)) :=
    Complex.continuous_re.measurable.comp (random_prime_measurable P c1 c2)
  exact (((contDiff_labelWeight hd J i).continuous.measurable.comp ha).sub
    ((polynomial delta J i (2 * S)).continuous.measurable.comp ha)).abs

theorem weighted_majorant_product {ι : Type*} (t : Finset ι) (delta : ℝ) (J S : ℕ)
    (P : ℝ) (c1 c2 : ι → ℕ → ℂ) (z : ℕ → ℂ) (W : ℝ) :
    W * (∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) z) =
      remainderScale delta J S ^ t.card *
        (W * ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) z‖ ^ (2 * S)) := by
  simp only [majorant, Finset.prod_mul_distrib, Finset.prod_const]
  ring

theorem random_weighted_majorant_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (delta : ℝ) (J S : ℕ) (P : ℝ) (s : Finset ℕ) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => steinhaus n ω)) phaseMeasure := by
  simp_rw [weighted_majorant_product]
  exact (random_weighted_power_product_integrable t ht P S s c1 c2 w).const_mul _

theorem random_weighted_majorant_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) (J S : ℕ) (P : ℝ) (s : Finset ℕ)
    (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ) (hs : ∀ n ∈ s, n ≠ 0)
    {B : ℝ} (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => steinhaus n ω) ∂phaseMeasure) ≤
      shortEnergy P s w * productBound delta J S t.card B := by
  simp_rw [weighted_majorant_product]
  rw [integral_const_mul]
  calc
    _ ≤ remainderScale delta J S ^ t.card *
        (shortEnergy P s w * ((S * t.card).factorial : ℝ) * B ^ (S * t.card)) :=
      mul_le_mul_of_nonneg_left (random_weighted_power_product_bound t ht P S s c1 c2 w hs hB)
        (pow_nonneg (remainderScale_nonneg hd J S) _)
    _ = _ := by unfold productBound; ring

theorem character_weighted_majorant_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) {delta : ℝ} (hd : 0 < delta) (J S : ℕ)
    (P x : ℝ) (s : Finset ℕ) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : x * (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => χ (n : ZMod q))) ≤
      shortEnergy P s w * productBound delta J S t.card B := by
  simp_rw [weighted_majorant_product]
  rw [uniformAverage_mul_left]
  calc
    _ ≤ remainderScale delta J S ^ t.card *
        (shortEnergy P s w * ((S * t.card).factorial : ℝ) * B ^ (S * t.card)) :=
      mul_le_mul_of_nonneg_left
        (character_weighted_power_product_bound t ht P x S s c1 c2 w hs ha hsize hB)
        (pow_nonneg (remainderScale_nonneg hd J S) _)
    _ = _ := by unfold productBound; ring

theorem weighted_remainder_product_le {ι : Type*} (t : Finset ι)
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (P : ℝ) (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ) (z : ℕ → ℂ)
    {W : ℝ} (hW : 0 ≤ W) :
    W * (∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) z) ≤
      W * (∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) z) := by
  apply mul_le_mul_of_nonneg_left _ hW
  exact Finset.prod_le_prod (fun i _ => remainder_nonneg _ _ _ _ _ _ _ _)
    (fun i _ => remainder_le_majorant hd hJ hS P (labels i) (c1 i) (c2 i) z)

theorem random_weighted_remainder_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (P : ℝ) (s : Finset ℕ) (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => steinhaus n ω))
      phaseMeasure := by
  apply (random_weighted_majorant_integrable t ht delta J S P s c1 c2 w).mono'
    ((short_square_measurable s w).mul (Finset.measurable_prod t
      (fun i _ => random_remainder_measurable hd J S P (labels i) (c1 i) (c2 i)))).aestronglyMeasurable
  filter_upwards with ω
  change ‖‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 * ∏ i ∈ t,
    remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (Finset.prod_nonneg (fun i _ => remainder_nonneg _ _ _ _ _ _ _ _)))]
  exact weighted_remainder_product_le t hd hJ hS P labels c1 c2 _ (sq_nonneg _)

theorem random_weighted_remainder_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (P : ℝ) (s : Finset ℕ) (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≠ 0) {B : ℝ} (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => steinhaus n ω)
      ∂phaseMeasure) ≤ shortEnergy P s w * productBound delta J S t.card B := by
  refine (integral_mono (random_weighted_remainder_integrable t ht hd hJ hS P s labels c1 c2 w)
    (random_weighted_majorant_integrable t ht delta J S P s c1 c2 w)
    (fun ω => weighted_remainder_product_le t hd hJ hS P labels c1 c2 _ (sq_nonneg _))).trans ?_
  exact random_weighted_majorant_bound t ht hd J S P s c1 c2 w hs hB

theorem character_weighted_remainder_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (P x : ℝ) (s : Finset ℕ)
    (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : x * (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => χ (n : ZMod q))) ≤
      shortEnergy P s w * productBound delta J S t.card B := by
  calc
    _ ≤ uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
        ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => χ (n : ZMod q))) := by
      unfold uniformAverage
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ =>
        weighted_remainder_product_le t hd hJ hS P labels c1 c2 _ (sq_nonneg _))) (by positivity)
    _ ≤ _ := character_weighted_majorant_bound t ht hd J S P x s c1 c2 w hs ha hsize hB

theorem random_majorant_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (delta : ℝ) (J S : ℕ) (P : ℝ) (c1 c2 : ι → ℕ → ℂ) :
    Integrable (fun ω => ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => steinhaus n ω))
      phaseMeasure := by
  simpa using random_weighted_majorant_integrable t ht delta J S P {1} c1 c2 (fun _ => 1)

theorem random_majorant_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) (J S : ℕ) (P : ℝ) (c1 c2 : ι → ℕ → ℂ)
    {B : ℝ} (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => steinhaus n ω) ∂phaseMeasure) ≤
      productBound delta J S t.card B := by
  simp_rw [majorant, Finset.prod_mul_distrib, Finset.prod_const]
  rw [integral_const_mul]
  simpa only [productBound, mul_assoc] using
    mul_le_mul_of_nonneg_left (random_power_product_bound t ht P S c1 c2 hB)
      (pow_nonneg (remainderScale_nonneg hd J S) t.card)

theorem character_majorant_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) {delta : ℝ} (hd : 0 < delta) (J S : ℕ)
    (P : ℝ) (c1 c2 : ι → ℕ → ℂ) (ha : ∀ p ∈ primesUpTo P, p.Coprime q)
    (hsize : (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q =>
      ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => χ (n : ZMod q))) ≤
      productBound delta J S t.card B := by
  simp_rw [majorant, Finset.prod_mul_distrib, Finset.prod_const]
  rw [uniformAverage_mul_left]
  simpa only [productBound, mul_assoc] using
    mul_le_mul_of_nonneg_left (character_power_product_bound t ht P S c1 c2 ha hsize hB)
      (pow_nonneg (remainderScale_nonneg hd J S) t.card)

theorem random_remainder_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (P : ℝ) (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ) :
    Integrable (fun ω => ∏ i ∈ t,
      remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => steinhaus n ω)) phaseMeasure := by
  simpa using random_weighted_remainder_integrable t ht hd hJ hS P {1} labels c1 c2 (fun _ => 1)

theorem random_remainder_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    {delta : ℝ} (hd : 0 < delta) {J S : ℕ} (hJ : 0 < J) (hS : 0 < S)
    (P : ℝ) (labels : ι → Fin (2 * J + 2)) (c1 c2 : ι → ℕ → ℂ)
    {B : ℝ} (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => steinhaus n ω)
      ∂phaseMeasure) ≤ productBound delta J S t.card B := by
  refine (integral_mono (random_remainder_integrable t ht hd hJ hS P labels c1 c2)
    (random_majorant_integrable t ht delta J S P c1 c2) (fun ω => ?_)).trans
    (random_majorant_bound t ht hd J S P c1 c2 hB)
  simpa only [one_mul] using
    weighted_remainder_product_le t hd hJ hS P labels c1 c2 (fun n => steinhaus n ω)
      (by norm_num : (0 : ℝ) ≤ 1)

theorem character_remainder_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (P : ℝ) (labels : ι → Fin (2 * J + 2))
    (c1 c2 : ι → ℕ → ℂ) (ha : ∀ p ∈ primesUpTo P, p.Coprime q)
    (hsize : (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q => ∏ i ∈ t,
      remainder delta J S P (labels i) (c1 i) (c2 i) (fun n => χ (n : ZMod q))) ≤
      productBound delta J S t.card B := by
  calc
    _ ≤ uniformAverage (fun χ : Character q =>
        ∏ i ∈ t, majorant delta J S P (c1 i) (c2 i) (fun n => χ (n : ZMod q))) := by
      unfold uniformAverage
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ _
      simpa only [one_mul] using
        weighted_remainder_product_le t hd hJ hS P labels c1 c2 (fun n => χ (n : ZMod q))
          (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ _ := character_majorant_bound t ht hd J S P c1 c2 ha hsize hB

end NField.Alignment.HarperRemainderProduct
