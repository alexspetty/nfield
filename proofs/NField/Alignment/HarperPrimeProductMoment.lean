/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperProductMoment

/-!
# Higher moments of products of the actual prime polynomials

The equal-exponent product estimate is applied to the literal prime and
prime-square polynomial in both probability models. Its integrability is
derived from the already proved even-moment integrability. A common prime
energy bound is kept explicit, and coefficient norms at most one give an
actual finite prime-energy majorant.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperPrimeProductMoment

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperProductMoment HarperPrimeEvenMoment
  HarperEvenMomentBound HarperSmoothDivisor CollisionMertensInput
  CollisionCharacterStructure SpectralRepulsion

def primeEnergy (P : ℝ) (c1 c2 : ℕ → ℂ) : ℝ :=
  ∑ p ∈ primesUpTo P, (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)

def shortEnergy (P : ℝ) (s : Finset ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2

def unitPrimeEnergy (P : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo P, ((1 : ℝ) / p + 6 / (p : ℝ) ^ 2)

theorem primeEnergy_nonneg (P : ℝ) (c1 c2 : ℕ → ℂ) : 0 ≤ primeEnergy P c1 c2 :=
  Finset.sum_nonneg fun p _ => add_nonneg
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))

theorem shortEnergy_nonneg (P : ℝ) (s : Finset ℕ) (w : ℕ → ℂ) : 0 ≤ shortEnergy P s w :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem primeEnergy_le_unit (P : ℝ) (c1 c2 : ℕ → ℂ)
    (h1 : ∀ p ∈ primesUpTo P, ‖c1 p‖ ≤ 1) (h2 : ∀ p ∈ primesUpTo P, ‖c2 p‖ ≤ 1) :
    primeEnergy P c1 c2 ≤ unitPrimeEnergy P := by
  apply Finset.sum_le_sum
  intro p hp
  apply add_le_add
  · exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (h1 p hp)) (Nat.cast_nonneg _)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) (h2 p hp) : ‖c2 p‖ ^ 2 ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)

theorem random_prime_measurable (P : ℝ) (c1 c2 : ℕ → ℂ) :
    Measurable (fun ω => primePolynomial P c1 c2 (fun n => steinhaus n ω)) := by
  unfold primePolynomial
  apply Finset.measurable_sum
  intro p _
  exact ((measurable_const.mul (steinhaus_measurable p)).div_const _).add
    ((measurable_const.mul (steinhaus_measurable (p ^ 2))).div_const _)

theorem short_square_measurable (s : Finset ℕ) (w : ℕ → ℂ) :
    Measurable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2) :=
  (Finset.measurable_sum s (fun n _ => measurable_const.mul (steinhaus_measurable n))).norm.pow_const 2

theorem random_weighted_power_product_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (P : ℝ) (S : ℕ) (s : Finset ℕ) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ^ (2 * S))
      phaseMeasure := by
  apply weighted_product_integrable t ht _ _ (fun _ => sq_nonneg _)
    (fun _ _ _ => by positivity) (short_square_measurable s w)
    (fun i _ => (random_prime_measurable P (c1 i) (c2 i)).norm.pow_const _)
  intro i _
  simpa only [← pow_mul, Nat.mul_assoc] using
    prime_even_moment_integrable P (S * t.card) s (c1 i) (c2 i) w

theorem random_weighted_power_product_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (P : ℝ) (S : ℕ) (s : Finset ℕ) (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≠ 0) {B : ℝ}
    (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ^ (2 * S)
      ∂phaseMeasure) ≤ shortEnergy P s w * ((S * t.card).factorial : ℝ) * B ^ (S * t.card) := by
  apply integral_weighted_product_le_common t ht _ _ (fun _ => sq_nonneg _)
    (fun _ _ _ => by positivity) (short_square_measurable s w)
    (fun i _ => (random_prime_measurable P (c1 i) (c2 i)).norm.pow_const _)
  · intro i _
    simpa only [← pow_mul, Nat.mul_assoc] using
      prime_even_moment_integrable P (S * t.card) s (c1 i) (c2 i) w
  · intro i hi
    simp only [← pow_mul, Nat.mul_assoc]
    refine (random_weighted_even_moment_bound P (S * t.card) s (c1 i) (c2 i) w hs).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by norm_num) (primeEnergy_nonneg P (c1 i) (c2 i))) (hB i hi) _)
      (mul_nonneg (shortEnergy_nonneg P s w) (Nat.cast_nonneg _))

theorem character_weighted_power_product_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) (P x : ℝ) (S : ℕ) (s : Finset ℕ)
    (c1 c2 : ι → ℕ → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : x * (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, 2 * primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) (fun n => χ (n : ZMod q))‖ ^ (2 * S)) ≤
      shortEnergy P s w * ((S * t.card).factorial : ℝ) * B ^ (S * t.card) := by
  apply average_weighted_product_le_common t ht _ _ (fun _ => sq_nonneg _) (fun _ _ _ => by positivity)
  intro i hi
  simp only [← pow_mul, Nat.mul_assoc]
  refine (character_weighted_even_moment_bound P x (S * t.card) s (c1 i) (c2 i) w hs ha hsize).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg (by norm_num) (primeEnergy_nonneg P (c1 i) (c2 i))) (hB i hi) _)
    (mul_nonneg (shortEnergy_nonneg P s w) (Nat.cast_nonneg _))

theorem random_power_product_integrable {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (P : ℝ) (S : ℕ) (c1 c2 : ι → ℕ → ℂ) :
    Integrable (fun ω => ∏ i ∈ t,
      ‖primePolynomial P (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ^ (2 * S)) phaseMeasure := by
  simpa using random_weighted_power_product_integrable t ht P S {1} c1 c2 (fun _ => 1)

theorem random_power_product_bound {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (P : ℝ) (S : ℕ) (c1 c2 : ι → ℕ → ℂ) {B : ℝ}
    (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    (∫ ω, ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ^ (2 * S)
      ∂phaseMeasure) ≤ ((S * t.card).factorial : ℝ) * B ^ (S * t.card) := by
  have h := integral_weighted_product_le_common (μ := phaseMeasure)
    (C := ((S * t.card).factorial : ℝ) * B ^ (S * t.card)) t ht (fun _ => 1)
    (fun i ω => ‖primePolynomial P (c1 i) (c2 i) (fun n => steinhaus n ω)‖ ^ (2 * S))
    (fun _ => by norm_num) (fun _ _ _ => by positivity) measurable_const
    (fun i _ => (random_prime_measurable P (c1 i) (c2 i)).norm.pow_const _)
    (fun i _ => by simpa only [one_mul, ← pow_mul, Nat.mul_assoc] using
      random_even_moment_integrable P (S * t.card) (c1 i) (c2 i))
  apply (by simpa only [one_mul] using h : _)
  intro i hi
  simp only [← pow_mul, Nat.mul_assoc]
  refine (random_even_moment_bound P (S * t.card) (c1 i) (c2 i)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (primeEnergy_nonneg P (c1 i) (c2 i)) (hB i hi) _) (Nat.cast_nonneg _)

theorem character_power_product_bound {q : ℕ} [NeZero q] {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) (P : ℝ) (S : ℕ) (c1 c2 : ι → ℕ → ℂ)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : (P ^ 2) ^ (S * t.card) < q)
    {B : ℝ} (hB : ∀ i ∈ t, primeEnergy P (c1 i) (c2 i) ≤ B) :
    uniformAverage (fun χ : Character q =>
      ∏ i ∈ t, ‖primePolynomial P (c1 i) (c2 i) (fun n => χ (n : ZMod q))‖ ^ (2 * S)) ≤
      ((S * t.card).factorial : ℝ) * B ^ (S * t.card) := by
  have h := average_weighted_product_le_common
    (C := ((S * t.card).factorial : ℝ) * B ^ (S * t.card)) t ht (fun _ : Character q => 1)
    (fun i χ => ‖primePolynomial P (c1 i) (c2 i) (fun n => χ (n : ZMod q))‖ ^ (2 * S))
    (fun _ => by norm_num) (fun _ _ _ => by positivity)
  apply (by simpa only [one_mul] using h : _)
  intro i hi
  simp only [← pow_mul, Nat.mul_assoc]
  refine (character_even_moment_bound P (S * t.card) (c1 i) (c2 i) ha hsize).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (primeEnergy_nonneg P (c1 i) (c2 i)) (hB i hi) _) (Nat.cast_nonneg _)

end NField.Alignment.HarperPrimeProductMoment
