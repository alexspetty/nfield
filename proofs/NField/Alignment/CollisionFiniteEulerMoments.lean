/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorArithmetic
import Mathlib.Algebra.DualNumber

/-!
# Finite Euler products retaining the logarithmic first moment

Dual numbers carry a mass and its first weighted moment through a finite
Euler product. This is finite algebra; no infinite product or limit is
assumed. The concrete arithmetic jet uses phi(k)/k^2 and log(k)+nu(k).
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionFiniteEulerMoments

open scoped Classical
open ArithmeticFunction CollisionConductorArithmetic TrivSqZeroExt

theorem multiplicative_divisor_euler {R : Type*} [CommSemiring R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, f k)=
      ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p+1), f (p^j) := by
  have h := (hf.mul isMultiplicative_zeta.natCast).multiplicative_factorization
    (f*(zeta : ArithmeticFunction R)) hn
  rw [coe_mul_zeta_apply] at h
  rw [h]
  apply Finset.prod_congr n.support_factorization
  intro p hp
  dsimp only
  rw [coe_mul_zeta_apply,Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

def massMoment (a b : ℝ) : DualNumber ℝ := (a,b)

theorem dual_product_mass_moment {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (∏ i ∈ s, massMoment (a i) (b i))=
      massMoment (∏ i ∈ s, a i) ((∏ i ∈ s, a i)*(∑ i ∈ s, b i/a i)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty,mul_zero]
    rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)),
      Finset.prod_insert hi,Finset.sum_insert hi]
    apply TrivSqZeroExt.ext
    · rfl
    · change a i*((∏ j ∈ s, a j)*(∑ j ∈ s, b j/a j))+b i*(∏ j ∈ s, a j)=
        (a i*(∏ j ∈ s, a j))*(b i/a i+∑ j ∈ s, b j/a j)
      have hai := ha i (Finset.mem_insert_self _ _)
      field_simp
      ring

def totientSquareWeight (k : ℕ) : ℝ := (k.totient : ℝ)/(k : ℝ)^2

def logarithmicMark (k : ℕ) : ℝ := Real.log k+nu k

def harmonicJet : ArithmeticFunction (DualNumber ℝ) where
  toFun k := (totientSquareWeight k,totientSquareWeight k*logarithmicMark k)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp [totientSquareWeight]

theorem totientSquareWeight_mul {m n : ℕ} (hmn : m.Coprime n) :
    totientSquareWeight (m*n)=totientSquareWeight m*totientSquareWeight n := by
  simp only [totientSquareWeight,Nat.totient_mul hmn,Nat.cast_mul,mul_pow,div_mul_div_comm]

theorem nu_coprime_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    nu (m*n)=nu m+nu n := by
  rw [nu,Nat.primeFactors_mul hm hn,Finset.sum_union hmn.disjoint_primeFactors]
  rfl

theorem logarithmicMark_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    logarithmicMark (m*n)=logarithmicMark m+logarithmicMark n := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [logarithmicMark,Nat.cast_mul,Real.log_mul hmR hnR,nu_coprime_add hm hn hmn]
  unfold logarithmicMark
  ring

theorem harmonicJet_multiplicative : harmonicJet.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  constructor
  · apply TrivSqZeroExt.ext <;> simp [harmonicJet,totientSquareWeight,logarithmicMark,nu]
  · intro m n hm hn hmn
    apply TrivSqZeroExt.ext
    · change totientSquareWeight (m*n)=totientSquareWeight m*totientSquareWeight n
      exact totientSquareWeight_mul hmn
    · change totientSquareWeight (m*n)*logarithmicMark (m*n)=
        totientSquareWeight m*(totientSquareWeight n*logarithmicMark n)+
          (totientSquareWeight m*logarithmicMark m)*totientSquareWeight n
      rw [totientSquareWeight_mul hmn,logarithmicMark_mul hm hn hmn]
      ring

theorem totientSquareWeight_prime_power {p : ℕ} (hp : p.Prime) (j : ℕ) :
    totientSquareWeight (p^(j+1))=(1-(p : ℝ)⁻¹)*((p : ℝ)⁻¹)^(j+1) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold totientSquareWeight
  rw [Nat.totient_prime_pow_succ hp,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hp.one_le,Nat.cast_one]
  push_cast
  simp only [pow_succ,mul_pow,inv_pow]
  field_simp

theorem logarithmicMark_prime_power {p : ℕ} (hp : p.Prime) (j : ℕ) :
    logarithmicMark (p^(j+1))=((j : ℝ)+1+((p : ℝ)-1)⁻¹)*Real.log p := by
  simp only [logarithmicMark,Nat.cast_pow,Real.log_pow,nu,Nat.primeFactors_pow_succ,
    hp.primeFactors,Finset.sum_singleton,Nat.cast_add,Nat.cast_one]
  ring

end NField.Alignment.CollisionFiniteEulerMoments
