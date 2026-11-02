/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Finite squarefree Euler identities

Multiplicativity and the vanishing of higher prime powers suffice for the
finite divisor product. This supplies actual Mobius twists for the
uniform conductor expansion.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSquarefreeEuler

open scoped BigOperators Classical ArithmeticFunction.zeta
open ArithmeticFunction

theorem squarefree_divisor_product (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hp : ∀ p : ℕ, p.Prime → ∀ k : ℕ, f (p^(k+2))=0) {q : ℕ} (hq : q≠0) :
    (∑ d ∈ q.divisors, f d)=∏ p ∈ q.primeFactors, (1+f p) := by
  have he : f*(ζ : ArithmeticFunction ℝ)=prodPrimeFactors (fun p => 1+f p) := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
      (hf.mul isMultiplicative_zeta.natCast) _ (IsMultiplicative.prodPrimeFactors _)).mpr
    intro p k hprime
    cases k with
    | zero => simp [hf.1]
    | succ k =>
      rw [coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hprime,
        prodPrimeFactors_apply (pow_ne_zero _ hprime.ne_zero),
        Nat.primeFactors_prime_pow (by omega) hprime,Finset.prod_singleton]
      rw [Finset.sum_range_succ',Finset.sum_range_succ']
      simp only [hf.1,Nat.zero_add,pow_zero,pow_one]
      have hz : (∑ x ∈ Finset.range k, f (p^(x+1+1)))=0 := by
        apply Finset.sum_eq_zero
        intro x _
        exact hp p hprime x
      rw [hz]
      ring
  rw [← coe_mul_zeta_apply,he,prodPrimeFactors_apply hq]

def realPower (s : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n=0 then 0 else (n : ℝ)^s
  map_zero' := by simp

theorem realPower_apply (s : ℝ) {n : ℕ} (hn : n≠0) : realPower s n=(n : ℝ)^s := by
  simp [realPower,hn]

theorem realPower_multiplicative (s : ℝ) : (realPower s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [realPower],?_⟩
  intro a b ha hb _
  rw [realPower_apply s (mul_ne_zero ha hb),realPower_apply s ha,realPower_apply s hb,Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

def moebiusTwist (s : ℝ) : ArithmeticFunction ℝ :=
  (moebius : ArithmeticFunction ℝ).pmul (realPower s)

theorem moebiusTwist_multiplicative (s : ℝ) : (moebiusTwist s).IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul (realPower_multiplicative s)

theorem moebiusTwist_apply (s : ℝ) {n : ℕ} (hn : n≠0) :
    moebiusTwist s n=(moebius n : ℝ)*(n : ℝ)^s := by
  simp only [moebiusTwist,pmul_apply,intCoe_apply,realPower_apply s hn]

theorem moebiusTwist_prime (s : ℝ) {p : ℕ} (hp : p.Prime) :
    moebiusTwist s p=-(p : ℝ)^s := by
  rw [moebiusTwist_apply s hp.ne_zero,moebius_apply_prime hp]
  push_cast
  ring

theorem moebiusTwist_prime_power (s : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    moebiusTwist s (p^(k+2))=0 := by
  rw [moebiusTwist_apply s (pow_ne_zero _ hp.ne_zero),
    moebius_apply_prime_pow hp (by omega),if_neg (by omega : k+2≠1)]
  simp

theorem moebius_power_divisor_product {q : ℕ} (hq : q≠0) (s : ℝ) :
    (∑ d ∈ q.divisors, (moebius d : ℝ)*(d : ℝ)^s)=
      ∏ p ∈ q.primeFactors, (1-(p : ℝ)^s) := by
  have he := squarefree_divisor_product (moebiusTwist s) (moebiusTwist_multiplicative s)
    (fun _ hp k => moebiusTwist_prime_power s hp k) hq
  convert! he using 1
  · apply Finset.sum_congr rfl
    intro d hd
    exact (moebiusTwist_apply s (Nat.pos_of_mem_divisors hd).ne').symm
  · apply Finset.prod_congr rfl
    intro p hp
    rw [moebiusTwist_prime s (Nat.prime_of_mem_primeFactors hp)]
    ring

def absMoebius : ArithmeticFunction ℝ where
  toFun n := |(moebius n : ℝ)|
  map_zero' := by simp

theorem absMoebius_multiplicative : absMoebius.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [absMoebius],?_⟩
  intro a b _ _ hab
  change |(moebius (a*b) : ℝ)|=|(moebius a : ℝ)| *|(moebius b : ℝ)|
  rw [isMultiplicative_moebius.2 hab]
  push_cast
  exact abs_mul _ _

def absoluteLinear : ArithmeticFunction ℝ :=
  absMoebius.pmul (ArithmeticFunction.pow 1 : ArithmeticFunction ℝ)

theorem absoluteLinear_apply (n : ℕ) : absoluteLinear n=|(moebius n : ℝ)| *(n : ℝ) := by
  simp [absoluteLinear,absMoebius]

theorem absoluteLinear_multiplicative : absoluteLinear.IsMultiplicative :=
  absMoebius_multiplicative.pmul isMultiplicative_pow.natCast

theorem absoluteLinear_prime {p : ℕ} (hp : p.Prime) : absoluteLinear p=p := by
  simp [absoluteLinear_apply,moebius_apply_prime hp]

theorem absoluteLinear_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    absoluteLinear (p^(k+2))=0 := by
  rw [absoluteLinear_apply,moebius_apply_prime_pow hp (by omega),if_neg (by omega : k+2≠1)]
  simp

theorem abs_moebius_divisor_product {q : ℕ} (hq : q≠0) :
    (∑ d ∈ q.divisors, |(moebius d : ℝ)| *(d : ℝ))=∏ p ∈ q.primeFactors, ((p : ℝ)+1) := by
  have he := squarefree_divisor_product absoluteLinear absoluteLinear_multiplicative
    (fun _ hp k => absoluteLinear_prime_power hp k) hq
  convert! he using 1
  · apply Finset.sum_congr rfl
    intro d _
    exact (absoluteLinear_apply d).symm
  · apply Finset.prod_congr rfl
    intro p hp
    rw [absoluteLinear_prime (Nat.prime_of_mem_primeFactors hp)]
    ring

end NField.Alignment.CollisionSquarefreeEuler
