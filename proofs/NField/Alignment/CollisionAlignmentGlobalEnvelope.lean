/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentGlobalSplit

/-!
# Global alignment envelopes with the absent-prime errors retained

The head is bounded by the same limiting prime factors as reset. The
full product includes its convergent absent-prime multiplier, and the
full logarithmic sum includes its independently bounded tail.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentGlobalEnvelope

open scoped Classical
open CollisionAlignmentGlobalSplit CollisionAlignmentEnvelopeSet CollisionAlignmentLocalBounds
open CollisionAlignmentLocalSeries CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum
open CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum CollisionAbsentPrimeProducts

theorem alignmentGlobalHeadProduct_nonneg (L : ℕ) (y : ℝ) :
    0 ≤ alignmentGlobalHeadProduct L y := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (envelopePrimeSet_prime hp).one_lt
  exact zero_le_one.trans (alignmentPrimeFactor_bounds hp1 _).1

theorem alignmentEulerProduct_nonneg (L : ℕ) : 0 ≤ alignmentEulerProduct L := by
  rw [alignment_global_product_split L 2]
  exact mul_nonneg (alignmentGlobalHeadProduct_nonneg L 2)
    (zero_le_one.trans (absentPrimeProduct_lower L 2))

theorem alignmentEulerLogSum_nonneg (L : ℕ) : 0 ≤ alignmentEulerLogSum L :=
  tsum_nonneg (alignmentPrimeLogTerm_nonneg L)

theorem alignmentGlobalHeadProduct_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 1 < y) :
    alignmentGlobalHeadProduct L y ≤
      limitingPrimeProduct y*Real.exp (Real.log (L : ℝ)/(y*Real.log y)) := by
  apply le_trans _ (envelopePrimeSet_product_bound hL hy)
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (envelopePrimeSet_prime hp).one_lt
    exact zero_le_one.trans (alignmentPrimeFactor_bounds hp1 _).1
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (envelopePrimeSet_prime hp).one_lt
    exact (alignmentPrimeFactor_bounds hp1 _).2

theorem alignmentGlobalHeadLogSum_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 1 < y) :
    alignmentGlobalHeadLogSum L y ≤ limitingPrimeLogSum y+2*Real.log (L : ℝ)/y := by
  apply le_trans _ (envelopePrimeSet_log_sum_bound hL hy)
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (envelopePrimeSet_prime hp).one_lt
  have h := mul_le_mul_of_nonneg_right (alignmentPrimeAverage_bounds hp1 (L.factorization p)).2
    (Real.log_nonneg hp1.le)
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using h

theorem alignmentEulerProduct_global_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 2 ≤ y) :
    alignmentEulerProduct L ≤
      limitingPrimeProduct y*Real.exp (Real.log (L : ℝ)/(y*Real.log y))*(1+4/y) := by
  have hy1 : 1 < y := by linarith
  have hhead := alignmentGlobalHeadProduct_bound hL hy1
  have htail : absentPrimeProduct L y ≤ 1+4/y := by
    have h := (le_abs_self _).trans (absent_prime_product_error_bound L hy)
    linarith
  rw [alignment_global_product_split L y]
  exact mul_le_mul hhead htail (zero_le_one.trans (absentPrimeProduct_lower L y))
    ((alignmentGlobalHeadProduct_nonneg L y).trans hhead)

theorem alignmentEulerLogSum_global_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 2 ≤ y) :
    alignmentEulerLogSum L ≤ limitingPrimeLogSum y+2*Real.log (L : ℝ)/y+
      2*(2*Real.log y+3)/y := by
  rw [alignment_global_log_sum_split L (by linarith : 1 ≤ y)]
  exact add_le_add (alignmentGlobalHeadLogSum_bound hL (by linarith))
    (absent_prime_tail_uniform_bounds L hy).2

end NField.Alignment.CollisionAlignmentGlobalEnvelope
