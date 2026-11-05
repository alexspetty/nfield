/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCandidateScale
import Mathlib.Data.Nat.Find

/-!
# The largest prime below a cutoff

An actual bounded search defines the prime. The unconditional relative
interval theorem proves that its ratio to the cutoff tends to one.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLargestPrime

open Filter
open CollisionPrimeDistribution

def largestPrime (Q : ℕ) : ℕ := Nat.findGreatest Nat.Prime Q

theorem largestPrime_prime {Q : ℕ} (hQ : 2 ≤ Q) : (largestPrime Q).Prime :=
  Nat.findGreatest_spec hQ Nat.prime_two

theorem largestPrime_le (Q : ℕ) : largestPrime Q ≤ Q := Nat.findGreatest_le Q

theorem prime_le_largestPrime {p Q : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) : p ≤ largestPrime Q := by
  by_contra h
  change ¬p ≤ Nat.findGreatest Nat.Prime Q at h
  exact Nat.findGreatest_is_greatest (by omega : Nat.findGreatest Nat.Prime Q < p) hpQ hp

theorem largestPrime_ratio_tendsto :
    Tendsto (fun Q : ℕ => (largestPrime Q : ℝ)/(Q : ℝ)) atTop (nhds 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hc0 : (0 : ℝ) < max b (1/2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hc1 : max b (1/2 : ℝ) < 1 := max_lt hb (by norm_num)
    filter_upwards [prime_in_relative_interval_nat hc0 hc1,eventually_ge_atTop (1 : ℕ)]
      with Q hprime hQ
    obtain ⟨p,hp,hnear,hpQ⟩ := hprime
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hpmax : (p : ℝ) ≤ (largestPrime Q : ℝ) := by
      exact_mod_cast prime_le_largestPrime hp hpQ
    apply (lt_div_iff₀ hQpos).mpr
    exact (mul_le_mul_of_nonneg_right (le_max_left b (1/2 : ℝ)) hQpos.le).trans_lt
      (hnear.trans_le hpmax)
  · intro b hb
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hpmax : (largestPrime Q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast largestPrime_le Q
    exact ((div_le_one hQpos).mpr hpmax).trans_lt hb

theorem largestPrime_tendsto : Tendsto largestPrime atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes N
  filter_upwards [eventually_ge_atTop p] with Q hpQ
  exact hNp.trans (prime_le_largestPrime hp hpQ)

theorem largestPrime_eventually_top :
    ∀ᶠ Q : ℕ in atTop, (largestPrime Q).Prime ∧ largestPrime Q ≤ Q ∧ Q < 2*largestPrime Q := by
  have hnear := largestPrime_ratio_tendsto.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 1))
  filter_upwards [hnear,eventually_ge_atTop (2 : ℕ)] with Q hnear hQ
  refine ⟨largestPrime_prime hQ,largestPrime_le Q,?_⟩
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h := (lt_div_iff₀ hQpos).mp hnear
  have h' : (Q : ℝ) < 2*(largestPrime Q : ℝ) := by linarith
  exact_mod_cast h'

theorem log_largestPrime_ratio_tendsto :
    Tendsto (fun Q : ℕ => Real.log (largestPrime Q)/Real.log Q) atTop (nhds 1) := by
  have hlogRatio := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    largestPrime_ratio_tendsto
  have hinvLog := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  have hprod := hlogRatio.mul hinvLog
  have hlim : Tendsto (fun Q : ℕ =>
      Real.log ((largestPrime Q : ℝ)/(Q : ℝ))*(Real.log Q)⁻¹+1) atTop (nhds 1) := by
    simpa using hprod.add_const 1
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hp := largestPrime_prime hQ
  have hpR : (0 : ℝ) < largestPrime Q := by exact_mod_cast hp.pos
  have hQR : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  rw [Real.log_div hpR.ne' (by linarith : (Q : ℝ) ≠ 0)]
  have hlog := (Real.log_pos hQR).ne'
  field_simp
  ring

end NField.Alignment.CollisionLargestPrime
