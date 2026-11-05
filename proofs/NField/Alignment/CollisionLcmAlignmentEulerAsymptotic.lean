/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmAlignmentTailSplit

/-!
# Asymptotics of the actual infinite lcm alignment Euler factors

The absent-prime product tends to one and its logarithmic sum tends to
zero even as the modulus varies through the actual cutoff periods. This
uses uniform proved bounds, not fixed-modulus convergence.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmAlignmentEulerAsymptotic

open scoped Classical
open Filter Asymptotics CollisionLcmFiniteProducts CollisionLcmFiniteLogSums
open CollisionLcmAlignmentTailSplit CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum
open CollisionOdometerRecurrence CollisionAbsentPrimeProducts CollisionAbsentPrimeSums
open CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum CollisionPositiveLogTail

theorem lcm_absent_product_tendsto :
    Tendsto (fun m : ℕ => absentPrimeProduct (cutoffPeriod m) m) atTop (nhds 1) := by
  have hz : Tendsto (fun m : ℕ => absentPrimeProduct (cutoffPeriod m) m-1) atTop (nhds 0) := by
    have hb : Tendsto (fun m : ℕ => (4 : ℝ)/m) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    apply squeeze_zero' _ _ hb
    · exact Filter.Eventually.of_forall (fun m => sub_nonneg.mpr (absentPrimeProduct_lower _ _))
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
      have h := absent_prime_product_error_bound (cutoffPeriod m) (by exact_mod_cast hm : (2 : ℝ) ≤ m)
      exact (le_abs_self _).trans h
  simpa only [sub_add_cancel,zero_add] using hz.add_const 1

theorem lcm_absent_log_sum_tendsto :
    Tendsto (fun m : ℕ => absentPrimeLogSum (cutoffPeriod m) m) atTop (nhds 0) := by
  have hb : Tendsto (fun m : ℕ => 2*positiveLogPrimitive m) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      (positiveLogPrimitive_tendsto_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m => absentPrimeLogSum_nonneg _ _)) _ hb
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have h := absent_prime_log_sum_bound (cutoffPeriod m) (by exact_mod_cast hm : (1 : ℝ) ≤ m)
  convert! h using 1
  unfold positiveLogPrimitive
  ring

theorem lcm_absent_log_sum_isLittleO :
    (fun m : ℕ => absentPrimeLogSum (cutoffPeriod m) m) =o[atTop] (fun m : ℕ => Real.log m) := by
  have hO : (fun m : ℕ => absentPrimeLogSum (cutoffPeriod m) m) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply isBigO_iff.mpr
    refine ⟨1,?_⟩
    have hb := lcm_absent_log_sum_tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb] with m hm
    simpa only [Real.norm_of_nonneg (absentPrimeLogSum_nonneg _ _),norm_one,mul_one] using hm.le
  exact hO.trans_isLittleO ((constant_isLittleO_log 1).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem lcm_alignment_euler_product_asymptotic :
    (fun m : ℕ => alignmentEulerProduct (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentKappa*Real.log m) := by
  have ht : (fun m : ℕ => absentPrimeProduct (cutoffPeriod m) m) ~[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isEquivalent_const_iff_tendsto (one_ne_zero : (1 : ℝ) ≠ 0)).mpr lcm_absent_product_tendsto
  have h := lcmAlignmentFiniteProduct_asymptotic.mul ht
  convert! h using 1
  · funext m
    exact lcm_alignment_product_split m
  · funext m
    simp only [Pi.mul_apply,mul_one]

theorem lcm_alignment_euler_log_sum_asymptotic :
    (fun m : ℕ => alignmentEulerLogSum (cutoffPeriod m)) ~[atTop] (fun m : ℕ => Real.log m) := by
  have h := lcmAlignmentFiniteLogSum_asymptotic.add_isLittleO lcm_absent_log_sum_isLittleO
  apply h.congr_left
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact (lcm_alignment_log_sum_split hm).symm

end NField.Alignment.CollisionLcmAlignmentEulerAsymptotic
