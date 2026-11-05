/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAbsentPrimeSums
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The literal absent-prime product and its uniform tail rate

Convergence is proved before bounding the infinite product. The same
constants apply for every modulus, including all choices of absent primes.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAbsentPrimeProducts

open scoped Classical
open Filter CollisionAbsentPrimeSums CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

def absentPrimeProduct (L : ℕ) (y : ℝ) : ℝ :=
  ∏' p : Nat.Primes, if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then
    alignmentPrimeFactor (p.val : ℝ) 0 else 1

def absentPrimeLogSum (L : ℕ) (y : ℝ) : ℝ := ∑' p : Nat.Primes, absentPrimeLogTerm L y p

theorem absentPrimeFactor_one_add (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    (if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then alignmentPrimeFactor (p.val : ℝ) 0 else 1)=
      1+absentPrimeMassTerm L y p := by
  have hp1 : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  unfold absentPrimeMassTerm
  split_ifs
  · exact alignmentPrimeFactor_zero hp1
  · ring

theorem absentPrimeProduct_multipliable (L : ℕ) (y : ℝ) :
    Multipliable (fun p : Nat.Primes =>
      if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then alignmentPrimeFactor (p.val : ℝ) 0 else 1) := by
  simp_rw [absentPrimeFactor_one_add]
  exact Real.multipliable_one_add_of_summable (absentPrimeMassTerm_summable L y)

theorem absentPrimeProduct_one_add (L : ℕ) (y : ℝ) :
    absentPrimeProduct L y=∏' p : Nat.Primes, (1+absentPrimeMassTerm L y p) := by
  unfold absentPrimeProduct
  exact tprod_congr (absentPrimeFactor_one_add L y)

theorem absentPrimeProduct_lower (L : ℕ) (y : ℝ) : 1 ≤ absentPrimeProduct L y := by
  have hP : Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (1+absentPrimeMassTerm L y p))
      atTop (nhds (∏' p : Nat.Primes, (1+absentPrimeMassTerm L y p))) :=
    (Real.multipliable_one_add_of_summable (absentPrimeMassTerm_summable L y)).hasProd
  rw [absentPrimeProduct_one_add]
  apply ge_of_tendsto hP
  exact Filter.Eventually.of_forall (fun s => Finset.one_le_prod (fun p hp => by
    linarith [absentPrimeMassTerm_nonneg L y p]))

theorem absentPrimeProduct_exp_bound (L : ℕ) (y : ℝ) :
    absentPrimeProduct L y ≤ Real.exp (∑' p : Nat.Primes, absentPrimeMassTerm L y p) := by
  have hs := absentPrimeMassTerm_summable L y
  rw [absentPrimeProduct_one_add]
  apply (Real.multipliable_one_add_of_summable hs).tprod_le_of_prod_le
  intro s
  exact (Real.prod_one_add_le_exp_sum s (absentPrimeMassTerm_nonneg L y)).trans
    (Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun p hp => absentPrimeMassTerm_nonneg L y p)))

theorem exp_sub_one_le_twice {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s-1 ≤ 2*s := by
  have hden : 0 < 2-s := by linarith
  have he := Real.exp_le_two_add_div_two_sub hs0 (by linarith : s < 2)
  have hr : (2+s)/(2-s) ≤ 1+2*s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  linarith

theorem absent_prime_product_error_bound (L : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    |absentPrimeProduct L y-1| ≤ 4/y := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 ≤ ∑' p : Nat.Primes, absentPrimeMassTerm L y p :=
    tsum_nonneg (absentPrimeMassTerm_nonneg L y)
  have hs := absent_prime_mass_sum_bound L hy
  have hs1 : (∑' p : Nat.Primes, absentPrimeMassTerm L y p) ≤ 1 := by
    have htwo : 2/y ≤ 1 := (div_le_one hy0).mpr hy
    exact hs.trans htwo
  rw [abs_of_nonneg (sub_nonneg.mpr (absentPrimeProduct_lower L y))]
  calc
    _ ≤ Real.exp (∑' p : Nat.Primes, absentPrimeMassTerm L y p)-1 :=
      sub_le_sub_right (absentPrimeProduct_exp_bound L y) 1
    _ ≤ 2*(∑' p : Nat.Primes, absentPrimeMassTerm L y p) := exp_sub_one_le_twice hs0 hs1
    _ ≤ 2*(2/y) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

theorem absentPrimeLogSum_nonneg (L : ℕ) (y : ℝ) : 0 ≤ absentPrimeLogSum L y :=
  tsum_nonneg (absentPrimeLogTerm_nonneg L y)

theorem absent_prime_tail_uniform_bounds (L : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    |absentPrimeProduct L y-1| ≤ 4/y ∧
      absentPrimeLogSum L y ≤ 2*(2*Real.log y+3)/y :=
  ⟨absent_prime_product_error_bound L hy,absent_prime_log_sum_bound L (by linarith)⟩

theorem absent_prime_product_isBigO (L : ℕ) :
    Asymptotics.IsBigO atTop (fun y : ℝ => absentPrimeProduct L y-1) (fun y : ℝ => 1/y) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨4,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  have hy0 : 0 ≤ y := by linarith
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (div_nonneg zero_le_one hy0)]
  convert! absent_prime_product_error_bound L hy using 1
  ring

theorem absent_prime_log_isBigO (L : ℕ) :
    Asymptotics.IsBigO atTop (absentPrimeLogSum L) (fun y : ℝ => Real.log (2*y)/y) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨10,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with y hy hl
  have hy0 : 0 < y := by linarith
  have hlog : Real.log y ≤ Real.log (2*y) := Real.log_le_log hy0 (by linarith)
  rw [Real.norm_of_nonneg (absentPrimeLogSum_nonneg L y),
    Real.norm_of_nonneg (div_nonneg (by linarith) hy0.le)]
  calc
    _ ≤ 2*(2*Real.log y+3)/y := absent_prime_log_sum_bound L (by linarith)
    _ ≤ 10*(Real.log (2*y)/y) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hy0.le
      linarith

theorem absent_prime_tail_estimates (L : ℕ) :
    Asymptotics.IsBigO atTop (fun y : ℝ => absentPrimeProduct L y-1) (fun y : ℝ => 1/y) ∧
      Asymptotics.IsBigO atTop (absentPrimeLogSum L) (fun y : ℝ => Real.log (2*y)/y) :=
  ⟨absent_prime_product_isBigO L,absent_prime_log_isBigO L⟩

end NField.Alignment.CollisionAbsentPrimeProducts
