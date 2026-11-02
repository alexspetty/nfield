/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRemainderProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Full products of partition factors and their Taylor approximations

Expansion over all nonempty subsets keeps every combination of Taylor
remainders. Grouping the subsets by cardinality gives the exact binomial
sum that will be estimated at the rounded Harper parameters.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperProductApproximation

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperPrimeProductMoment HarperRemainderProduct
  HarperPartition HarperPartitionDerivative HarperPartitionTaylor HarperPrimeTaylorComparison

theorem abs_prod_sub_le_subsets {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b r : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hr : ∀ i ∈ s, |b i - a i| ≤ r i) :
    |(∏ i ∈ s, b i) - ∏ i ∈ s, a i| ≤
      ∑ t ∈ s.powerset.erase ∅, ∏ i ∈ t, r i := by
  classical
  have he := Finset.prod_add (fun i => b i - a i) a s
  simp only [sub_add_cancel] at he
  have h0 : (∅ : Finset ι) ∈ s.powerset := Finset.empty_mem_powerset s
  calc
    _ = |∑ t ∈ s.powerset.erase ∅,
        (∏ i ∈ t, (b i - a i)) * ∏ i ∈ s \ t, a i| := by
      rw [he, ← Finset.sum_erase_add _ _ h0]
      simp
    _ ≤ ∑ t ∈ s.powerset.erase ∅,
        |(∏ i ∈ t, (b i - a i)) * ∏ i ∈ s \ t, a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have hts := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      calc
        _ ≤ (∏ i ∈ t, r i) * 1 :=
          mul_le_mul (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => hr i (hts hi)))
            (Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i hi => ha i (Finset.mem_sdiff.mp hi).1))
            (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
            (Finset.prod_nonneg (fun i hi => (abs_nonneg _).trans (hr i (hts hi))))
        _ = _ := mul_one _

theorem sum_nonempty_subsets_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ℕ → ℝ) :
    (∑ t ∈ s.powerset.erase ∅, f t.card) =
      ∑ j ∈ Finset.range (s.card + 1), if j = 0 then 0 else (s.card.choose j : ℝ) * f j := by
  classical
  have he : (∑ t ∈ s.powerset.erase ∅, f t.card) =
      ∑ t ∈ s.powerset, (if t.card = 0 then 0 else f t.card) := by
    rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]
    simp only [Finset.card_empty, ↓reduceIte, add_zero]
    apply Finset.sum_congr rfl
    intro t ht
    rw [if_neg (Finset.card_ne_zero.mpr
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1))]
  rw [he, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_powersetCard j s (fun k => if k = 0 then 0 else f k)]
  split_ifs <;> simp [nsmul_eq_mul]

def errorSum (delta : ℝ) (J S A : ℕ) (B : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (A + 1), if j = 0 then 0 else (A.choose j : ℝ) * productBound delta J S j B

theorem errorSum_eq_subsets (delta : ℝ) (J S A : ℕ) (B : ℝ) :
    errorSum delta J S A B =
      ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅, productBound delta J S t.card B := by
  simpa [errorSum] using (sum_nonempty_subsets_card (Finset.univ : Finset (Fin A))
    (fun j => productBound delta J S j B)).symm

def smoothValue (delta : ℝ) (J A : ℕ) (P : ℝ) (labels : Fin A → Fin (2 * J + 2))
    (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ) : ℝ :=
  boxWeight delta J (fun i => primeArgument P (c1 i) (c2 i) z) labels

theorem smoothValue_nonneg {delta : ℝ} (hd : 0 < delta) (J A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ) :
    0 ≤ smoothValue delta J A P labels c1 c2 z := boxWeight_nonneg hd J _ labels

theorem smoothValue_le_one {delta : ℝ} (hd : 0 < delta) (J A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ) :
    smoothValue delta J A P labels c1 c2 z ≤ 1 := by
  unfold smoothValue boxWeight
  exact Finset.prod_le_one (fun i _ => labelWeight_nonneg hd J (labels i) _)
    (fun i _ => labelWeight_le_one hd J (labels i) _)

theorem weighted_product_error {delta : ℝ} (hd : 0 < delta) (J S A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ)
    {W : ℝ} (hW : 0 ≤ W) :
    |W * smoothValue delta J A P labels c1 c2 z -
        W * taylorValue delta J (2 * S) A P labels c1 c2 z| ≤
      ∑ t ∈ (Finset.univ : Finset (Fin A)).powerset.erase ∅,
        W * ∏ i ∈ t, remainder delta J S P (labels i) (c1 i) (c2 i) z := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hW, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hW
  rw [abs_sub_comm]
  unfold smoothValue boxWeight taylorValue
  apply abs_prod_sub_le_subsets
  · intro i _
    rw [abs_of_nonneg (labelWeight_nonneg hd J (labels i) _)]
    exact labelWeight_le_one hd J (labels i) _
  · intro i _
    exact (abs_sub_comm _ _).le

theorem random_smooth_measurable {delta : ℝ} (hd : 0 < delta) (J A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) :
    Measurable (fun ω => smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω)) := by
  unfold smoothValue boxWeight
  apply Finset.measurable_prod
  intro i _
  exact (contDiff_labelWeight hd J (labels i)).continuous.measurable.comp
    (Complex.continuous_re.measurable.comp (random_prime_measurable P (c1 i) (c2 i)))

theorem random_weighted_smooth_integrable {delta : ℝ} (hd : 0 < delta) (J A : ℕ) (P : ℝ)
    (s : Finset ℕ) (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω)) phaseMeasure := by
  have hI : Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2) phaseMeasure := by
    simpa using HarperPrimeEvenMoment.prime_even_moment_integrable P 0 s (fun _ => 0) (fun _ => 0) w
  apply hI.mono' ((short_square_measurable s w).mul
    (random_smooth_measurable hd J A P labels c1 c2)).aestronglyMeasurable
  filter_upwards with ω
  change ‖‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
    smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (smoothValue_nonneg hd J A P labels c1 c2 _))]
  exact mul_le_of_le_one_right (sq_nonneg _) (smoothValue_le_one hd J A P labels c1 c2 _)

end NField.Alignment.HarperProductApproximation
