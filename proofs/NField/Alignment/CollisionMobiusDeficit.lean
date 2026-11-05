/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteRegrouping
import NField.Alignment.CollisionSquarefreeEuler

/-!
# The actual negative Mobius divisor budget

The truncated divisor sum retains the positive unit divisor. Its remaining
negative contribution is bounded by all negative squarefree divisors.
This is a finite statement, separate from the infinite Dirichlet series.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMobiusDeficit

open scoped BigOperators Classical
open ArithmeticFunction CollisionFiniteRegrouping CollisionSquarefreeEuler CollisionMassInverse

def negativeMobius (j : ℕ) : ℝ := (|(moebius j : ℝ)|-(moebius j : ℝ))/2
def divisorDeficit (m : ℕ) : ℝ :=
  if 2 ≤ m then (2 : ℝ)^m.primeFactors.card/2-1 else 0

theorem negativeMobius_nonneg (j : ℕ) : 0 ≤ negativeMobius j := by
  exact div_nonneg (sub_nonneg.mpr (le_abs_self _)) (by norm_num)

theorem negativeMobius_one : negativeMobius 1=0 := by simp [negativeMobius]

theorem absoluteMobius_divisor_count {m : ℕ} (hm : 0 < m) :
    (∑ j ∈ m.divisors, |(moebius j : ℝ)|)=(2 : ℝ)^m.primeFactors.card := by
  have he := squarefree_divisor_product absMoebius absMoebius_multiplicative
    (fun p hp k => by
      simp [absMoebius,moebius_apply_prime_pow hp (by omega : k+2≠0)]) hm.ne'
  change (∑ j ∈ m.divisors, absMoebius j)=_
  rw [he]
  convert! Finset.prod_const (s := m.primeFactors) (b := (2 : ℝ)) using 1
  apply Finset.prod_congr rfl
  intro p hp
  norm_num [absMoebius,moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]

theorem negativeMobius_divisor_sum {m : ℕ} (hm : 2 ≤ m) :
    (∑ j ∈ m.divisors, negativeMobius j)=(2 : ℝ)^m.primeFactors.card/2 := by
  simp only [negativeMobius,← Finset.sum_div,Finset.sum_sub_distrib,
    absoluteMobius_divisor_count (by omega : 0 < m),moebius_divisor_sum,
    if_neg (by omega : m≠1),sub_zero]

theorem partialMobius_term_lower {J : ℕ} (hJ : 1 ≤ J) (j : ℕ) :
    (if j ≤ J then (moebius j : ℝ) else 0) ≥
      (if j=1 then (1 : ℝ) else 0)-negativeMobius j := by
  by_cases hj : j=1
  · simp [hj,hJ,negativeMobius_one]
  rw [if_neg hj]
  by_cases hjJ : j ≤ J
  · rw [if_pos hjJ]
    have h := neg_abs_le (moebius j : ℝ)
    unfold negativeMobius
    linarith
  · rw [if_neg hjJ]
    linarith [negativeMobius_nonneg j]

theorem partialMobius_lower {m J : ℕ} (hm : 2 ≤ m) (hJ : 1 ≤ J) :
    -divisorDeficit m ≤ partialMobius J m := by
  have h := Finset.sum_le_sum (s := m.divisors) (fun j _ => partialMobius_term_lower hJ j)
  rw [Finset.sum_sub_distrib,negativeMobius_divisor_sum hm] at h
  have hone : (∑ j ∈ m.divisors, if j=1 then (1 : ℝ) else 0)=1 := by
    simp [Nat.one_mem_divisors.mpr (by omega : m≠0)]
  rw [hone] at h
  unfold divisorDeficit partialMobius
  rw [if_pos hm]
  linarith

theorem divisorDeficit_literal {m : ℕ} (hm : 2 ≤ m) :
    divisorDeficit m=(2 : ℝ)^(m.primeFactors.card-1)-1 := by
  have hc : 1 ≤ m.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  have he : m.primeFactors.card=(m.primeFactors.card-1)+1 := by omega
  unfold divisorDeficit
  rw [if_pos hm]
  nth_rw 1 [he]
  rw [pow_succ]
  ring

theorem divisorDeficit_nonneg (m : ℕ) : 0 ≤ divisorDeficit m := by
  by_cases hm : 2 ≤ m
  · rw [divisorDeficit_literal hm]
    have h : (1 : ℝ) ≤ 2^(m.primeFactors.card-1) := one_le_pow₀ (by norm_num)
    linarith
  · simp [divisorDeficit,hm]

theorem divisorDeficit_prime_power {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    divisorDeficit (p^k)=0 := by
  have hpow : 2 ≤ p^k := (hp.two_le).trans (Nat.le_self_pow hk.ne' p)
  simp [divisorDeficit,hpow,Nat.primeFactors_prime_pow hk.ne' hp]

end NField.Alignment.CollisionMobiusDeficit
