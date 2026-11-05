/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteProductDeficit
import NField.Alignment.CollisionLimitingPrimeProduct
import NField.Alignment.CollisionLimitingPrimeLogSum

/-!
# Asymptotics of the finite lcm prime products

The exact product ratios tend to one by the proved summed local losses.
Combining them with the limiting prime product gives the sharp finite-
product coefficient. The absent-prime alignment tail is handled separately.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmFiniteProducts

open scoped Classical
open Filter Asymptotics CollisionFiniteProductDeficit CollisionLimitingPrimeProduct
open CollisionLimitingPrimeLogSum CollisionMertensInput CollisionOdometerRecurrence
open CollisionLcmPrimeLosses CollisionLcmFactorErrors CollisionResetEulerProduct
open CollisionResetLocalFactors CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

def lcmAlignmentFiniteProduct (m : ℕ) : ℝ := ∏ p ∈ Nat.primesLE m,
  alignmentPrimeFactor (p : ℝ) ((cutoffPeriod m).factorization p)

def lcmAlignmentFiniteLogSum (m : ℕ) : ℝ := ∑ p ∈ Nat.primesLE m,
  alignmentPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p)*Real.log p

theorem primesUpTo_natCast (m : ℕ) : primesUpTo (m : ℝ)=Nat.primesLE m := by
  rw [primesUpTo_eq_primesLE_floor,Nat.floor_natCast]

theorem limitingPrimeProduct_nat_formula (m : ℕ) :
    limitingPrimeProduct (m : ℝ)=∏ p ∈ Nat.primesLE m, (1+(p : ℝ)⁻¹) := by
  unfold limitingPrimeProduct
  rw [primesUpTo_natCast]

theorem lcmResetEulerProduct_formula (m : ℕ) :
    resetEulerProduct (cutoffPeriod m)=∏ p ∈ Nat.primesLE m,
      resetPrimeFactor (p : ℝ) ((cutoffPeriod m).factorization p) := by
  unfold resetEulerProduct
  rw [cutoffPeriod_primeFactors]

theorem lcmResetEulerLogSum_formula (m : ℕ) :
    resetEulerLogSum (cutoffPeriod m)=∑ p ∈ Nat.primesLE m,
      resetPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p)*Real.log p := by
  unfold resetEulerLogSum
  rw [cutoffPeriod_primeFactors]

theorem lcmAlignmentFiniteProduct_relative_error (m : ℕ) :
    0 ≤ 1-lcmAlignmentFiniteProduct m/limitingPrimeProduct m ∧
      1-lcmAlignmentFiniteProduct m/limitingPrimeProduct m ≤ lcmAlignmentFactorLoss m := by
  rw [limitingPrimeProduct_nat_formula]
  apply finite_relative_product_deficit
  · intro p hp
    positivity
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    linarith [(alignmentPrimeFactor_bounds hp1 ((cutoffPeriod m).factorization p)).1]
  · intro p hp
    exact (alignmentPrimeFactor_bounds
      (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt) _).2

theorem lcmResetEulerProduct_relative_error (m : ℕ) :
    0 ≤ 1-resetEulerProduct (cutoffPeriod m)/limitingPrimeProduct m ∧
      1-resetEulerProduct (cutoffPeriod m)/limitingPrimeProduct m ≤ lcmResetFactorLoss m := by
  rw [limitingPrimeProduct_nat_formula,lcmResetEulerProduct_formula]
  apply finite_relative_product_deficit
  · intro p hp
    positivity
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    linarith [(resetPrimeFactor_bounds hp1 ((cutoffPeriod m).factorization p)).1]
  · intro p hp
    exact (resetPrimeFactor_bounds
      (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt) _).2

theorem inverse_sqrt_nat_tendsto (c : ℝ) :
    Tendsto (fun m : ℕ => c/Real.sqrt m) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem tendsto_one_of_sqrt_error (f : ℕ → ℝ)
    (hf0 : ∀ m, 0 ≤ 1-f m) (hf : ∀ m, 4 ≤ m → 1-f m ≤ 3/Real.sqrt m) :
    Tendsto f atTop (nhds 1) := by
  have hz : Tendsto (fun m : ℕ => 1-f m) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall hf0) _ (inverse_sqrt_nat_tendsto 3)
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
    exact hf m hm
  have h := hz.const_sub 1
  simpa only [sub_sub_cancel,sub_zero] using h

theorem lcmAlignmentFiniteProduct_ratio_tendsto :
    Tendsto (fun m : ℕ => lcmAlignmentFiniteProduct m/limitingPrimeProduct m) atTop (nhds 1) := by
  apply tendsto_one_of_sqrt_error
  · exact fun m => (lcmAlignmentFiniteProduct_relative_error m).1
  · exact fun m hm => (lcmAlignmentFiniteProduct_relative_error m).2.trans
      (lcmAlignmentFactorLoss_bound hm)

theorem lcmResetEulerProduct_ratio_tendsto :
    Tendsto (fun m : ℕ => resetEulerProduct (cutoffPeriod m)/limitingPrimeProduct m) atTop (nhds 1) := by
  apply tendsto_one_of_sqrt_error
  · exact fun m => (lcmResetEulerProduct_relative_error m).1
  · exact fun m hm => (lcmResetEulerProduct_relative_error m).2.trans
      (lcmResetFactorLoss_bound hm)

theorem lcmAlignmentFiniteProduct_asymptotic :
    lcmAlignmentFiniteProduct ~[atTop] (fun m : ℕ => alignmentKappa*Real.log m) :=
  (isEquivalent_of_tendsto_one lcmAlignmentFiniteProduct_ratio_tendsto).trans
    (limitingPrimeProduct_asymptotic.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem lcmResetEulerProduct_asymptotic :
    (fun m : ℕ => resetEulerProduct (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentKappa*Real.log m) :=
  (isEquivalent_of_tendsto_one lcmResetEulerProduct_ratio_tendsto).trans
    (limitingPrimeProduct_asymptotic.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ)))

end NField.Alignment.CollisionLcmFiniteProducts
