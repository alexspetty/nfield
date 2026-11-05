/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMertensInput
import NField.Alignment.CollisionZetaMoments
import NField.Alignment.CollisionLocalFactorLosses

/-!
# The limiting logarithmic prime sum

Changing the Mertens denominator p to p-1 adds a bounded nonnegative
correction. Absolute summability supplies that bound independently of
the cutoff, so the exact logarithmic leading coefficient remains one.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLimitingPrimeLogSum

open scoped Classical
open Filter Asymptotics CollisionMertensInput CollisionZetaMoments

def limitingPrimeLogSum (x : ℝ) : ℝ := ∑ p ∈ primesUpTo x, Real.log p/((p : ℝ)-1)

theorem prime_log_correction_bounds {p : ℝ} (hp : 2 ≤ p) :
    0 ≤ Real.log p/(p-1)-Real.log p/p ∧
      Real.log p/(p-1)-Real.log p/p ≤ 2*(Real.log p/p^2) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-1 := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have he : Real.log p/(p-1)-Real.log p/p=(1/(p*(p-1)))*Real.log p := by
    field_simp
    ring
  have hr : 1/(p*(p-1)) ≤ 2/p^2 := by
    apply (div_le_div_iff₀ (mul_pos hp0 hpm) (sq_pos_of_pos hp0)).mpr
    nlinarith
  rw [he]
  refine ⟨by positivity,?_⟩
  convert! mul_le_mul_of_nonneg_right hr hl using 1
  ring

theorem limitingPrimeLogSum_correction_bound (x : ℝ) :
    |limitingPrimeLogSum x-logPrimeSum x| ≤ 2*logSquareMoment := by
  have he : limitingPrimeLogSum x-logPrimeSum x=
      ∑ p ∈ primesUpTo x, (Real.log p/((p : ℝ)-1)-Real.log p/(p : ℝ)) := by
    rw [Finset.sum_sub_distrib]
    rfl
  have hn : 0 ≤ ∑ p ∈ primesUpTo x, (Real.log p/((p : ℝ)-1)-Real.log p/(p : ℝ)) := by
    apply Finset.sum_nonneg
    intro p hp
    exact (prime_log_correction_bounds (by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le)).1
  rw [he,abs_of_nonneg hn]
  calc
    _ ≤ ∑ p ∈ primesUpTo x, 2*logSquareTerm p := by
      apply Finset.sum_le_sum
      intro p hp
      exact (prime_log_correction_bounds (by exact_mod_cast (primesUpTo_mem.mp hp).1.two_le)).2
    _ = 2*(∑ p ∈ primesUpTo x, logSquareTerm p) := by rw [Finset.mul_sum]
    _ ≤ 2*logSquareMoment := mul_le_mul_of_nonneg_left
      (logSquareTerm_summable.sum_le_tsum _ (fun p hp =>
        div_nonneg (Real.log_natCast_nonneg p) (sq_nonneg _))) (by norm_num)

theorem limitingPrimeLogSum_error_bound {x : ℝ} (hx : 1 ≤ x) :
    |limitingPrimeLogSum x-Real.log x| ≤ 2*logSquareMoment+Real.log 4+4 := by
  have h := abs_sub_le (limitingPrimeLogSum x) (logPrimeSum x) (Real.log x)
  linarith [limitingPrimeLogSum_correction_bound x,logPrimeSum_error_bound hx]

theorem limitingPrimeLogSum_error_isBigO :
    (fun x : ℝ => limitingPrimeLogSum x-Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨2*logSquareMoment+Real.log 4+4,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs,abs_one,mul_one] using limitingPrimeLogSum_error_bound hx

theorem constant_isLittleO_log (c : ℝ) :
    (fun _ : ℝ => c) =o[atTop] Real.log :=
  (isLittleO_const_id_atTop c).comp_tendsto Real.tendsto_log_atTop

theorem limitingPrimeLogSum_asymptotic : limitingPrimeLogSum ~[atTop] Real.log := by
  exact limitingPrimeLogSum_error_isBigO.trans_isLittleO (constant_isLittleO_log 1)

end NField.Alignment.CollisionLimitingPrimeLogSum
