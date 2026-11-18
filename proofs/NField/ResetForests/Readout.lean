/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
/-! # Signed readouts and the exact coarsening loss

These identities concern arbitrary signed readings. Positivity is imposed
on source work, never on the readings. Zero-work directions must have zero
reading. No uniform arithmetic growth estimate is an input to these lemmas.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators

def readoutCost {ι : Type*} (s : Finset ι) (e d : ι → ℝ) : ℝ :=
  ∑ i ∈ s, d i ^ 2 / e i

theorem readout_cost_nonneg {ι : Type*} (s : Finset ι) (e d : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) : 0 ≤ readoutCost s e d := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (sq_nonneg _) (he i hi)

/-- Weighted Cauchy with all signed readings and zero-work cases retained. -/
theorem signed_readout_bound {ι : Type*} (s : Finset ι) (e d : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i)
    (hz : ∀ i ∈ s, e i = 0 → d i = 0) :
    (∑ i ∈ s, d i)^2 ≤ (∑ i ∈ s, e i) * readoutCost s e d := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s he
    (fun i hi => div_nonneg (sq_nonneg _) (he i hi))
  intro i hi
  by_cases hzero : e i = 0
  · simp [hzero, hz i hi hzero]
  · exact le_of_eq (by field_simp)

/-- Combining a fixed group cannot increase the positive cost. -/
theorem coarsened_readout_cost_le {ι : Type*} (s : Finset ι) (e d : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i)
    (hz : ∀ i ∈ s, e i = 0 → d i = 0) :
    (∑ i ∈ s, d i)^2 / (∑ i ∈ s, e i) ≤ readoutCost s e d := by
  have hE := Finset.sum_nonneg he
  by_cases hzero : (∑ i ∈ s, e i) = 0
  · simp [hzero, readout_cost_nonneg s e d he]
  · apply (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mpr
    simpa [mul_comm] using signed_readout_bound s e d he hz

theorem pair_variance_expansion {ei ej di dj : ℝ} (hi : ei ≠ 0) (hj : ej ≠ 0) :
    ei * ej * (di/ei-dj/ej)^2 = di^2/ei*ej + ei*(dj^2/ej) - 2*di*dj := by
  field_simp [hi, hj]
  ring

/-- The loss before division by total work, using both ordered pairs. -/
theorem signed_cost_loss_ordered {ι : Type*} (s : Finset ι) (e d : ι → ℝ)
    (he : ∀ i ∈ s, 0 < e i) :
    (∑ i ∈ s, e i) * readoutCost s e d - (∑ i ∈ s, d i)^2 =
      (1/2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        e i * e j * (d i/e i-d j/e j)^2 := by
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :=
    pair_variance_expansion (he i hi).ne' (he j hj).ne' (di := d i) (dj := d j)
  have hexpand :
      (∑ i ∈ s, ∑ j ∈ s, e i*e j*(d i/e i-d j/e j)^2) =
      ∑ i ∈ s, ∑ j ∈ s,
        (d i^2/e i*e j + e i*(d j^2/e j) - 2*d i*d j) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_congr rfl (fun j hj => hpair i hi j hj)
  rw [hexpand]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, readoutCost]
  ring

theorem symmetric_pair_sum {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f : ι → ι → ℝ)
    (hs : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i)
    (hd : ∀ i ∈ s, f i i = 0) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) =
      2 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j := by
  classical
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      f i j = (if i < j then f i j else 0) +
        (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst j; simp [hd i hi]
    · simp [h, not_lt.mpr h.le, hs i hi j hj]
  have hexpand : (∑ i ∈ s, ∑ j ∈ s, f i j) =
      (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0) +
      (∑ i ∈ s, ∑ j ∈ s, if j < i then f j i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => hp i hi j hj)
  rw [hexpand, Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
  simp only [Finset.sum_filter]
  ring

/-- The exact unordered-pair formula printed in Proposition12.2. -/
theorem signed_cost_loss {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (e d : ι → ℝ) (he : ∀ i ∈ s, 0 < e i) :
    (∑ i ∈ s, e i) * readoutCost s e d - (∑ i ∈ s, d i)^2 =
      ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j),
        e i*e j*(d i/e i-d j/e j)^2 := by
  rw [signed_cost_loss_ordered s e d he]
  rw [symmetric_pair_sum s (fun i j => e i*e j*(d i/e i-d j/e j)^2)
    (by intro i _ j _; ring) (by intro i _; simp)]
  ring

/-- The exact amount lost when one group is read as one direction. -/
theorem group_cost_decrease {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (e d : ι → ℝ) (he : ∀ i ∈ s, 0 < e i)
    (hE : (∑ i ∈ s, e i) ≠ 0) :
    readoutCost s e d - (∑ i ∈ s, d i)^2/(∑ i ∈ s, e i) =
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j),
        e i*e j*(d i/e i-d j/e j)^2)/(∑ i ∈ s, e i) := by
  rw [← signed_cost_loss s e d he]
  field_simp

/-- Summing the exact loss for every block of a fixed grouping. -/
theorem grouped_cost_decrease {ι : Type*} [LinearOrder ι]
    (groups : Finset (Finset ι)) (e d : ι → ℝ)
    (he : ∀ B ∈ groups, ∀ i ∈ B, 0 < e i)
    (hE : ∀ B ∈ groups, (∑ i ∈ B, e i) ≠ 0) :
    (∑ B ∈ groups, readoutCost B e d) -
        (∑ B ∈ groups, (∑ i ∈ B, d i)^2/(∑ i ∈ B, e i)) =
      ∑ B ∈ groups,
        (∑ i ∈ B, ∑ j ∈ B.filter (fun j => i < j),
          e i*e j*(d i/e i-d j/e j)^2)/(∑ i ∈ B, e i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun B hB => group_cost_decrease B e d (he B hB) (hE B hB))

end NField.ResetForests.Core
