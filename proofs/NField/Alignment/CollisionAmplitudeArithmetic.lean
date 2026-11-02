/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReciprocalBudget
import NField.Alignment.CollisionJordanVariance

/-!
# Jordan-three and the positive harmonic-seed convolution

These arithmetic identities support the exact amplitude refinement. The
Euler product is defined independently of the desired amplitude budget.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeArithmetic

open scoped BigOperators Classical ArithmeticFunction.zeta
open ArithmeticFunction Filter
open CollisionRemainderDynamics CollisionMassReadout CollisionReciprocalBudget

def deltaThree (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (1-((p : ℝ)^3)⁻¹)

def jordanThree : ArithmeticFunction ℝ :=
  (ArithmeticFunction.pow 3 : ArithmeticFunction ℝ).pmul
    (prodPrimeFactors (fun p => 1-((p : ℝ)^3)⁻¹))

theorem jordanThree_euler_product {q : ℕ} (hq : q≠0) :
    jordanThree q=(q : ℝ)^3*deltaThree q := by
  simp [jordanThree, deltaThree, prodPrimeFactors_apply hq]

theorem jordanThree_multiplicative : jordanThree.IsMultiplicative :=
  isMultiplicative_pow.natCast.pmul (IsMultiplicative.prodPrimeFactors _)

@[simp] theorem jordanThree_zero : jordanThree 0=0 := jordanThree.map_zero
@[simp] theorem jordanThree_one : jordanThree 1=1 := jordanThree_multiplicative.1

theorem deltaThree_pos (q : ℕ) : 0<deltaThree q := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp3 : (1 : ℝ)<(p : ℝ)^3 := by
    calc
      _ < (2 : ℝ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 3
  have hi := inv_lt_one_of_one_lt₀ hp3
  linarith

theorem jordanThree_pos {q : ℕ} (hq : 0<q) : 0<jordanThree q := by
  rw [jordanThree_euler_product hq.ne']
  exact mul_pos (by positivity) (deltaThree_pos q)

theorem jordanThree_prime_power_succ {p : ℕ} (hp : p.Prime) (i : ℕ) :
    jordanThree (p^(i+1))=((p : ℝ)^(i+1))^3-((p : ℝ)^i)^3 := by
  rw [jordanThree_euler_product (pow_ne_zero _ hp.ne_zero), deltaThree,
    Nat.primeFactors_prime_pow (by omega) hp]
  simp only [Finset.prod_singleton, pow_succ]
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp

theorem sum_jordanThree_prime_power {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (∑ j ∈ Finset.range (i+1), jordanThree (p^j))=((p : ℝ)^i)^3 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, jordanThree_prime_power_succ hp]
    ring

theorem jordanThree_mul_zeta : jordanThree*(ζ : ArithmeticFunction ℝ)=
    (ArithmeticFunction.pow 3 : ArithmeticFunction ℝ) := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (jordanThree_multiplicative.mul isMultiplicative_zeta.natCast) _
    isMultiplicative_pow.natCast).mpr
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sum_jordanThree_prime_power hp]
  simp

theorem sum_jordanThree_divisors (q : ℕ) :
    (∑ d ∈ q.divisors, jordanThree d)=(q : ℝ)^3 := by
  rw [← coe_mul_zeta_apply, jordanThree_mul_zeta]
  simp

def harmonicKernel (n : ℕ) : ℝ := (harmonic (n-1) : ℝ)/(n : ℝ)^2

theorem harmonicKernel_nonneg (n : ℕ) : 0≤harmonicKernel n := by
  unfold harmonicKernel
  exact div_nonneg (by exact_mod_cast harmonic_nonneg (n-1)) (sq_nonneg _)

theorem harmonicKernel_divisor (n : ℕ) (hn : 0<n) :
    harmonicKernel n=∑ d ∈ n.divisors, collisionWeight d/((n/d : ℕ) : ℝ)^3 := by
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (∑ d ∈ n.divisors, collisionWeight d/((n/d : ℕ) : ℝ)^3) =
      (∑ d ∈ n.divisors, (d : ℝ)^3*collisionWeight d)/(n : ℝ)^3 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hq : 0<n/d := Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_mem_divisors hd)
    have hqR : (((n/d : ℕ) : ℝ))≠0 := by exact_mod_cast hq.ne'
    have hmul : (((n/d : ℕ) : ℝ))*(d : ℝ)=(n : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    apply (div_eq_div_iff (pow_ne_zero _ hqR) (pow_ne_zero _ hnR)).mpr
    rw [← hmul]
    ring
  rw [he, reciprocal_budget hn, harmonicKernel]
  field_simp

end NField.Alignment.CollisionAmplitudeArithmetic
