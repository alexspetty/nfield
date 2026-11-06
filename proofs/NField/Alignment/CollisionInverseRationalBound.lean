/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionInverseRemainder
import NField.Alignment.CollisionVarianceEnclosure
import NField.Alignment.CollisionConductorEnclosure

/-!
# An explicit rational error for amplitude-to-mass recovery

The elementary harmonic weight bound gives a numerical constant four in
the logarithmic amplitude majorant. It yields a computable inverse-tail
bound without estimating zeta derivatives or using the target mass itself.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionInverseRationalBound

open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance
open CollisionHarmonicSeed CollisionAmplitudeTail CollisionPositiveLogTail
open CollisionDivisorSeries CollisionPositiveConstants CollisionInverseRemainder
open CollisionFiniteRegrouping CollisionVarianceEnclosure

theorem inverseSquare_tsum_le_two : (∑' j : ℕ, zetaKernel 2 j) ≤ 2 := by
  have hs := zetaKernel_summable (by norm_num : (1 : ℝ) < 2)
  have he := hs.sum_add_tsum_nat_add 2
  have hz (j : ℕ) : zetaKernel 2 j = 1/(j : ℝ)^2 := zetaKernel_nat (by norm_num) j
  have hz0 : zetaKernel 2 0=0 := by rw [hz]; norm_num
  have hz1 : zetaKernel 2 1=1 := by rw [hz]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hz0, hz1, zero_add] at he
  have hb : (∑' n : ℕ, zetaKernel 2 (n+2)) ≤ 1 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_one, div_one] using
      inverseSquare_shift_bound (by norm_num : 1 ≤ (1 : ℕ))
  linarith

theorem positiveLog_nat_summable : Summable (fun j : ℕ => positiveLogKernel j) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.add_assoc] using positiveLog_shift_summable (by norm_num : 1 ≤ (1 : ℕ))

theorem positiveLog_tsum_le_four : (∑' j : ℕ, positiveLogKernel j) ≤ 4 := by
  have he := positiveLog_nat_summable.sum_add_tsum_nat_add 2
  have hz0 : positiveLogKernel (0 : ℕ)=0 := by norm_num [positiveLogKernel]
  have hz1 : positiveLogKernel (1 : ℕ)=1 := by norm_num [positiveLogKernel]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hz0, hz1, zero_add] at he
  have hb : (∑' n : ℕ, positiveLogKernel (n+2 : ℕ)) ≤ 3 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_one, Real.log_one,
      mul_zero, zero_add, div_one] using positiveLog_shift_bound (by norm_num : 1 ≤ (1 : ℕ))
  linarith

theorem collisionWeight_multiple_log_bound {q : ℕ} (hq : 1 ≤ q) (j : ℕ) :
    collisionWeight (q*j) ≤
      (Real.log q*zetaKernel 2 j+positiveLogKernel j)/(q : ℝ)^2 := by
  by_cases hj : j=0
  · subst j
    simp [positiveLogKernel]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hjR : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
  have h := collisionWeight_log_bound (show 1 ≤ q*j by nlinarith [Nat.pos_of_ne_zero hj])
  have hz : zetaKernel 2 j = 1/(j : ℝ)^2 := zetaKernel_nat (by norm_num) j
  convert h using 1
  rw [Nat.cast_mul, Real.log_mul hqR.ne' hjR.ne', hz]
  unfold positiveLogKernel
  field_simp
  ring

theorem amplitude_four_log_bound {q : ℕ} (hq : 2 ≤ q) :
    amplitude q ≤ 4*positiveLogKernel q := by
  have hq0 : 0 < q := by omega
  have hs := collisionWeight_summable.comp_injective
    (fun a b h => Nat.mul_left_cancel hq0 h)
  have hm := (((zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).mul_left
    (Real.log q)).add positiveLog_nat_summable).div_const ((q : ℝ)^2)
  have ht := hs.tsum_le_tsum (collisionWeight_multiple_log_bound (by omega : 1 ≤ q)) hm
  rw [tsum_multiples hq0] at ht
  change amplitude q ≤ _ at ht
  rw [tsum_div_const, Summable.tsum_add
    ((zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).mul_left (Real.log q))
    positiveLog_nat_summable, tsum_mul_left] at ht
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left inverseSquare_tsum_le_two (Real.log_natCast_nonneg q))
    positiveLog_tsum_le_four
  apply ht.trans
  apply (div_le_div_of_nonneg_right hb (sq_nonneg (q : ℝ))).trans
  unfold positiveLogKernel
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (q : ℝ))
  nlinarith [Real.log_natCast_nonneg q]

theorem amplitude_scaled_four_log_bound {d j : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j) :
    amplitude (d*j) ≤ 4/(d : ℝ)^2*
      (Real.log d*zetaKernel 2 j+positiveLogKernel j) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have h := amplitude_four_log_bound (show 2 ≤ d*j by nlinarith)
  have hz : zetaKernel 2 j = 1/(j : ℝ)^2 := zetaKernel_nat (by norm_num) j
  convert h using 1
  unfold positiveLogKernel
  rw [Nat.cast_mul, Real.log_mul hdR.ne' hjR.ne', hz]
  field_simp
  ring

theorem amplitude_multiple_four_tail_bound {d J : ℕ} (hd : 2 ≤ d) (hJ : 1 ≤ J) :
    (∑' n, amplitude (d*(n+J+1))) ≤
      4*(Real.log d+2*Real.log J+3)/((d : ℝ)^2*(J : ℝ)) := by
  have hm := ((inverseSquare_shift_summable J).mul_left (Real.log d)).add
    (positiveLog_shift_summable hJ)
  have ht := (amplitude_multiple_shift_summable (by omega : 0 < d) J).tsum_le_tsum
    (fun n => amplitude_scaled_four_log_bound hd (by omega : 1 ≤ n+J+1))
    (hm.mul_left (4/(d : ℝ)^2))
  rw [tsum_mul_left, Summable.tsum_add
    ((inverseSquare_shift_summable J).mul_left (Real.log d))
    (positiveLog_shift_summable hJ), tsum_mul_left] at ht
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left (inverseSquare_shift_bound hJ) (Real.log_natCast_nonneg d))
    (positiveLog_shift_bound hJ)
  have hu := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4/(d : ℝ)^2)
  apply ht.trans
  convert hu using 1
  ring

theorem log_le_binary_bound {n b : ℕ} (hn : 1 ≤ n) (hb : 2*n ≤ 2^b) :
    Real.log n ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (Real.log_le_log hnR (by nlinarith : (n : ℝ) ≤ 2*n)).trans
    (log_twice_le_binary_bound hn hb)

def rationalInverseError (d J bd bj : ℕ) : ℝ :=
  4*((bd : ℝ)+2*(bj : ℝ)+3)/((d : ℝ)^2*(J : ℝ))

theorem beta_inverse_rational_bound {d Q bd bj : ℕ}
    (hd : 2 ≤ d) (hdQ : d ≤ Q) (hbd : 2*d ≤ 2^bd) (hbj : 2*(Q/d) ≤ 2^bj) :
    |beta d Q-collisionWeight d| ≤ rationalInverseError d (Q/d) bd bj := by
  have hJ : 1 ≤ Q/d := Nat.div_pos hdQ (by omega)
  apply (beta_inverse_remainder_norm (by omega : 0 < d) Q).trans
  apply (amplitude_multiple_four_tail_bound hd hJ).trans
  unfold rationalInverseError
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hdlog := log_le_binary_bound (by omega : 1 ≤ d) hbd
  have hjlog := log_le_binary_bound hJ hbj
  linarith

theorem mass_mem_inverse_enclosure {d Q bd bj : ℕ} {lower upper : ℝ}
    (hd : 2 ≤ d) (hdQ : d ≤ Q) (hbd : 2*d ≤ 2^bd) (hbj : 2*(Q/d) ≤ 2^bj)
    (hl : lower ≤ beta d Q) (hu : beta d Q ≤ upper) :
    collisionWeight d ∈ Set.Icc (max 0 (lower-rationalInverseError d (Q/d) bd bj))
      (upper+rationalInverseError d (Q/d) bd bj) := by
  have h := abs_le.mp (beta_inverse_rational_bound hd hdQ hbd hbj)
  refine ⟨max_le (collisionWeight_nonneg d) ?_, ?_⟩ <;> linarith

theorem collision_mass_recovery_enclosure {d Q bd bj : ℕ} (M : ℕ)
    (hd : 2 ≤ d) (hdQ : d ≤ Q) (hbd : 2*d ≤ 2^bd) (hbj : 2*(Q/d) ≤ 2^bj) :
    collisionWeight d ∈ Set.Icc
      (max 0 (CollisionConductorEnclosure.betaRawLower d Q M-rationalInverseError d (Q/d) bd bj))
      (CollisionConductorEnclosure.betaUpper d Q M+rationalInverseError d (Q/d) bd bj) := by
  have h := CollisionConductorEnclosure.beta_raw_enclosure d Q M
  exact mass_mem_inverse_enclosure hd hdQ hbd hbj h.1 h.2

end NField.Alignment.CollisionInverseRationalBound
