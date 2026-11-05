/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralEnergyError

/-!
# Quantitative tails of the actual full conductor amplitudes

The logarithmic conductor correction is bounded by log(q). This gives a
uniform pointwise amplitude majorant and a certified infinite tail bound.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeTail

open scoped BigOperators Classical
open Filter
open CollisionJordanVariance CollisionConductorArithmetic CollisionZetaMoments
open CollisionSpectralNuBounds CollisionSpectralEnergyError CollisionPositiveLogTail

def positiveUnit (n : ℕ) : ℝ := if n=0 then 0 else 1
def amplitudeLogConstant : ℝ := 2*amplitudeLeading+residualConstant
def amplitudeTail (Q : ℝ) : ℝ := ∑' q : ℕ, if Q < (q : ℝ) then amplitude q else 0

theorem nu_le_log {q : ℕ} (hq : 0 < q) : nu q ≤ Real.log q := by
  have hp0 : ∀ p ∈ q.primeFactors, (p : ℝ)≠0 := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpPos : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hrad : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq q.prod_primeFactors_dvd
  calc
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      apply div_le_self (Real.log_natCast_nonneg p)
      linarith
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := (Real.log_prod hp0).symm
    _ ≤ _ := Real.log_le_log hpPos hrad

theorem positiveUnit_zero : positiveUnit 0=0 := by simp [positiveUnit]

theorem positiveUnit_nonneg (n : ℕ) : 0 ≤ positiveUnit n := by
  unfold positiveUnit
  split_ifs <;> norm_num

theorem positiveUnit_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, positiveUnit n)=(N : ℝ) := by
  have he : (∑ n ∈ Finset.Ioc 0 N, positiveUnit n)=∑ _n ∈ Finset.Ioc 0 N, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_neg (ne_of_gt (Finset.mem_Ioc.mp hn).1)
  rw [he]
  simp

theorem positiveUnit_tail_summable {Q : ℝ} (hQ : 1 ≤ Q) :
    Summable (fun q : ℕ => if Q < (q : ℝ) then positiveLogTerm positiveUnit q else 0) :=
  positiveLog_tail_summable_of_nat positiveUnit_zero positiveUnit_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) hQ (fun N => by rw [positiveUnit_partial_sum,one_mul])

theorem positiveUnit_tail_bound {Q : ℝ} (hQ : 1 ≤ Q) :
    positiveLogTail positiveUnit Q ≤ (2*Real.log Q+3)/Q := by
  simpa only [one_mul] using positiveLog_tail_bound_of_nat positiveUnit_zero positiveUnit_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) hQ (fun N => by rw [positiveUnit_partial_sum,one_mul])

theorem amplitudeLogConstant_pos : 0 < amplitudeLogConstant := by
  unfold amplitudeLogConstant
  positivity [spectralLeading_pos,residualConstant_pos]

theorem amplitude_log_bound {q : ℕ} (hq : 2 ≤ q) :
    amplitude q ≤ amplitudeLogConstant*positiveLogKernel q := by
  have hq0 : 0 < q := by omega
  have hL := Real.log_natCast_nonneg q
  have hr : amplitude q ≤ leadingAmplitude q+|residualAmplitude q| := by
    have h := le_abs_self (residualAmplitude q)
    unfold residualAmplitude at h ⊢
    linarith
  calc
    _ ≤ leadingAmplitude q+|residualAmplitude q| := hr
    _ ≤ amplitudeLeading*Real.log q/(q : ℝ)^2+
        (residualConstant+amplitudeLeading*nu q)/(q : ℝ)^2 :=
      add_le_add (leadingAmplitude_bound hq0) (residualAmplitude_bound hq)
    _ ≤ amplitudeLeading*Real.log q/(q : ℝ)^2+
        (residualConstant+amplitudeLeading*Real.log q)/(q : ℝ)^2 := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (sq_nonneg (q : ℝ))
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (nu_le_log hq0) spectralLeading_pos.le)
    _ = (2*amplitudeLeading*Real.log q+residualConstant)/(q : ℝ)^2 := by ring
    _ ≤ (2*amplitudeLeading+residualConstant)*(1+Real.log q)/(q : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg (q : ℝ))
      nlinarith [spectralLeading_pos,mul_nonneg residualConstant_pos.le hL]
    _ = _ := by unfold amplitudeLogConstant positiveLogKernel; ring

theorem amplitude_tail_term_bound {Q : ℝ} (hQ : 1 ≤ Q) (q : ℕ) :
    (if Q < (q : ℝ) then amplitude q else 0) ≤
      amplitudeLogConstant*(if Q < (q : ℝ) then positiveLogTerm positiveUnit q else 0) := by
  by_cases hq : Q < (q : ℝ)
  · have hq2 : 2 ≤ q := by
      have h : (1 : ℝ) < q := hQ.trans_lt hq
      have hn : 1 < q := by exact_mod_cast h
      omega
    simpa only [if_pos hq,positiveLogTerm,positiveUnit,if_neg (by omega : q≠0),mul_one] using
      amplitude_log_bound hq2
  · simp only [if_neg hq,mul_zero,le_refl]

theorem amplitude_tail_summable {Q : ℝ} (hQ : 1 ≤ Q) :
    Summable (fun q : ℕ => if Q < (q : ℝ) then amplitude q else 0) := by
  apply Summable.of_nonneg_of_le _ (amplitude_tail_term_bound hQ)
    ((positiveUnit_tail_summable hQ).mul_left amplitudeLogConstant)
  intro q
  split_ifs
  · exact amplitude_nonneg q
  · rfl

theorem amplitude_tail_nonneg (Q : ℝ) : 0 ≤ amplitudeTail Q := by
  apply tsum_nonneg
  intro q
  split_ifs
  · exact amplitude_nonneg q
  · rfl

theorem amplitude_tail_comparison {Q : ℝ} (hQ : 1 ≤ Q) :
    amplitudeTail Q ≤ amplitudeLogConstant*positiveLogTail positiveUnit Q := by
  have h := (amplitude_tail_summable hQ).tsum_le_tsum (amplitude_tail_term_bound hQ)
    ((positiveUnit_tail_summable hQ).mul_left amplitudeLogConstant)
  rw [tsum_mul_left] at h
  exact h

theorem amplitude_tail_bound {Q : ℝ} (hQ : 1 ≤ Q) :
    amplitudeTail Q ≤ amplitudeLogConstant*(2*Real.log Q+3)/Q := by
  calc
    _ ≤ amplitudeLogConstant*positiveLogTail positiveUnit Q := amplitude_tail_comparison hQ
    _ ≤ amplitudeLogConstant*((2*Real.log Q+3)/Q) :=
      mul_le_mul_of_nonneg_left (positiveUnit_tail_bound hQ) amplitudeLogConstant_pos.le
    _ = _ := by ring

theorem amplitude_tail_isBigO :
    Asymptotics.IsBigO atTop amplitudeTail (fun Q : ℝ => Real.log Q/Q) := by
  have hcomp : Asymptotics.IsBigO atTop amplitudeTail (positiveLogTail positiveUnit) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨amplitudeLogConstant,?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Q hQ
    rw [Real.norm_of_nonneg (amplitude_tail_nonneg Q),
      Real.norm_of_nonneg (positiveLog_tail_nonneg positiveUnit_nonneg Q)]
    exact amplitude_tail_comparison hQ
  exact hcomp.trans (positiveLog_tail_isBigO positiveUnit_zero positiveUnit_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) (fun N => by rw [positiveUnit_partial_sum,one_mul]))

end NField.Alignment.CollisionAmplitudeTail
