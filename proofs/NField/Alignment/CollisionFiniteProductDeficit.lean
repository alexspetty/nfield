/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmFactorErrors

/-!
# Finite product deficits and local relative errors

The product inequality preserves every finite factor. It converts the
proved summed relative losses into an error on the actual product ratio.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionFiniteProductDeficit

open scoped Classical

theorem finite_product_deficit {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr0 : ∀ i ∈ s, 0 ≤ r i) (hr1 : ∀ i ∈ s, r i ≤ 1) :
    0 ≤ 1-(∏ i ∈ s, r i) ∧ 1-(∏ i ∈ s, r i) ≤ ∑ i ∈ s, (1-r i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hr0 a (Finset.mem_insert_self a s)
    have ha1 := hr1 a (Finset.mem_insert_self a s)
    have hs0 := fun i hi => hr0 i (Finset.mem_insert_of_mem hi)
    have hs1 := fun i hi => hr1 i (Finset.mem_insert_of_mem hi)
    have h := ih hs0 hs1
    have hP0 : 0 ≤ ∏ i ∈ s, r i := Finset.prod_nonneg hs0
    have hP1 : (∏ i ∈ s, r i) ≤ 1 := by linarith
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    constructor
    · have hp := mul_le_mul ha1 hP1 hP0 (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    · have hm := mul_le_mul_of_nonneg_right ha1 h.1
      nlinarith [h.2]

theorem finite_relative_product_deficit {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (ha0 : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) :
    0 ≤ 1-(∏ i ∈ s, a i)/(∏ i ∈ s, b i) ∧
      1-(∏ i ∈ s, a i)/(∏ i ∈ s, b i) ≤ ∑ i ∈ s, (b i-a i)/b i := by
  have hr0 : ∀ i ∈ s, 0 ≤ a i/b i := fun i hi => div_nonneg (ha0 i hi) (hb i hi).le
  have hr1 : ∀ i ∈ s, a i/b i ≤ 1 := fun i hi => (div_le_one (hb i hi)).mpr (hab i hi)
  have h := finite_product_deficit s (fun i => a i/b i) hr0 hr1
  rw [Finset.prod_div_distrib] at h
  have he : (∑ i ∈ s, (1-a i/b i))=∑ i ∈ s, (b i-a i)/b i := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [(hb i hi).ne']
  rwa [he] at h

end NField.Alignment.CollisionFiniteProductDeficit
