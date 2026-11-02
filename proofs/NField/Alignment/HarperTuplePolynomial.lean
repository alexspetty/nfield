/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-!
# A coefficient bound for ordered prime and prime-square choices

The generating polynomial is the literal sum of `X_i + X_i^2` over a finite
index type. A partial-derivative recurrence bounds every coefficient of its
`k`th power. The bound is weighted by `2^k`, avoiding truncated subtraction
in the exponent; the later prime-factorization correspondence converts it
to a factorial times a power of the number of square choices.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperTuplePolynomial

open scoped BigOperators
open MvPolynomial

variable {ι : Type*} [Fintype ι]

def countingPolynomial (ι : Type*) [Fintype ι] : MvPolynomial ι ℕ :=
  ∑ i, (X i + X i ^ 2)

def exponentWeight (d : ι →₀ ℕ) : ℕ := ∑ i, d i

theorem exponentWeight_add_single (d : ι →₀ ℕ) (i : ι) :
    exponentWeight (d + Finsupp.single i 1) = exponentWeight d + 1 := by
  classical
  simp [exponentWeight, Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]

theorem countingPolynomial_pderiv (i : ι) :
    pderiv i (countingPolynomial ι) = 1 + 2 * X i := by
  classical
  unfold countingPolynomial
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem coefficient_recurrence (k : ℕ) (d : ι →₀ ℕ) (i : ι) :
    coeff (d + Finsupp.single i 1) (countingPolynomial ι ^ (k + 1)) * (d i + 1) =
      (k + 1) * (coeff d (countingPolynomial ι ^ k) +
        2 * coeff d (countingPolynomial ι ^ k * X i)) := by
  classical
  have hc : coeff (d + Finsupp.single i 1) (countingPolynomial ι ^ (k + 1)) * (d i + 1) =
      coeff d (pderiv i (countingPolynomial ι ^ (k + 1))) := by
    simpa using (coeff_pderiv (i := i) (countingPolynomial ι ^ (k + 1)) d).symm
  rw [hc, pderiv_pow, countingPolynomial_pderiv, Nat.add_sub_cancel]
  have he : ((k + 1 : ℕ) : MvPolynomial ι ℕ) * countingPolynomial ι ^ k * (1 + 2 * X i) =
      C (k + 1) * (countingPolynomial ι ^ k + C 2 * (countingPolynomial ι ^ k * X i)) := by
    have hC (n : ℕ) : C n = (n : MvPolynomial ι ℕ) := by
      simp
    simp only [hC]
    ring
  rw [he, coeff_C_mul, coeff_add, coeff_C_mul]

theorem coefficient_zero_succ (k : ℕ) :
    coeff 0 (countingPolynomial ι ^ (k + 1)) = 0 := by
  change constantCoeff (countingPolynomial ι ^ (k + 1)) = 0
  simp [countingPolynomial]

/-- A uniform coefficient estimate; no assumption about tuple multiplicities occurs. -/
theorem coefficient_factorial_bound (k : ℕ) (d : ι →₀ ℕ) :
    coeff d (countingPolynomial ι ^ k) * 2 ^ k ≤ k.factorial * 2 ^ exponentWeight d := by
  classical
  induction k generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp [exponentWeight]
      · simp [coeff_one, Ne.symm hd]
  | succ k ih =>
      by_cases hd : d = 0
      · subst d
        simp only [coefficient_zero_succ, zero_mul, zero_le]
      have hex : ∃ i, d i ≠ 0 := by
        by_contra! h
        exact hd (Finsupp.ext h)
      obtain ⟨i, hi⟩ := hex
      let m := d - Finsupp.single i 1
      have hdm : m + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
      rw [← hdm]
      have hr := coefficient_recurrence k m i
      by_cases hm : m i = 0
      · have hn : i ∉ m.support := by simpa only [Finsupp.mem_support_iff] using not_not_intro hm
        rw [hm, zero_add, mul_one, coeff_mul_X', if_neg hn, mul_zero, add_zero] at hr
        calc
          _ = ((k + 1) * (coeff m (countingPolynomial ι ^ k) * 2 ^ k)) * 2 := by
            rw [hr, pow_succ]
            ring
          _ ≤ ((k + 1) * (k.factorial * 2 ^ exponentWeight m)) * 2 :=
            Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left (k + 1) (ih m))
          _ = _ := by rw [Nat.factorial_succ, exponentWeight_add_single, pow_succ]; ring
      · let e := m - Finsupp.single i 1
        have hem : e + Finsupp.single i 1 = m := Finsupp.sub_add_single_one_cancel hm
        have hx : coeff m (countingPolynomial ι ^ k * X i) = coeff e (countingPolynomial ι ^ k) := by
          rw [← hem, coeff_mul_X]
        rw [hx] at hr
        have htwo : 2 ≤ m i + 1 := by omega
        have hsmall : 2 * coeff (m + Finsupp.single i 1) (countingPolynomial ι ^ (k + 1)) ≤
            (k + 1) * (coeff m (countingPolynomial ι ^ k) +
              2 * coeff e (countingPolynomial ι ^ k)) := by
          calc
            _ ≤ coeff (m + Finsupp.single i 1) (countingPolynomial ι ^ (k + 1)) * (m i + 1) := by
              simpa only [mul_comm] using Nat.mul_le_mul_left
                (coeff (m + Finsupp.single i 1) (countingPolynomial ι ^ (k + 1))) htwo
            _ = _ := hr
        have hbound : 2 * (coeff (m + Finsupp.single i 1)
            (countingPolynomial ι ^ (k + 1)) * 2 ^ (k + 1)) ≤
            2 * ((k + 1).factorial * 2 ^ exponentWeight (m + Finsupp.single i 1)) := by
          calc
            _ ≤ ((k + 1) * (coeff m (countingPolynomial ι ^ k) +
                2 * coeff e (countingPolynomial ι ^ k))) * 2 ^ (k + 1) := by
              simpa only [mul_assoc] using Nat.mul_le_mul_right (2 ^ (k + 1)) hsmall
            _ = (k + 1) * (2 * (coeff m (countingPolynomial ι ^ k) * 2 ^ k) +
                4 * (coeff e (countingPolynomial ι ^ k) * 2 ^ k)) := by rw [pow_succ]; ring
            _ ≤ (k + 1) * (2 * (k.factorial * 2 ^ exponentWeight m) +
                4 * (k.factorial * 2 ^ exponentWeight e)) := by
              exact Nat.mul_le_mul_left (k + 1) (Nat.add_le_add
                (Nat.mul_le_mul_left 2 (ih m)) (Nat.mul_le_mul_left 4 (ih e)))
            _ = _ := by
              rw [← hem]
              simp only [exponentWeight_add_single, Nat.factorial_succ, pow_succ]
              ring
        omega

def atomExponent (a : ι × Bool) : ι →₀ ℕ := Finsupp.single a.1 (if a.2 then 2 else 1)

def tupleExponent (k : ℕ) (t : Fin k → ι × Bool) : ι →₀ ℕ := ∑ j, atomExponent (t j)

def squareCount (k : ℕ) (t : Fin k → ι × Bool) : ℕ :=
  (Finset.univ.filter (fun j => (t j).2 = true)).card

def exponentMultiplicity (k : ℕ) (d : ι →₀ ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin k → ι × Bool => tupleExponent k t = d)).card

theorem countingPolynomial_atom_sum :
    countingPolynomial ι = ∑ a : ι × Bool, monomial (atomExponent a) 1 := by
  classical
  rw [countingPolynomial, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, atomExponent, Bool.false_eq_true, ↓reduceIte]
  rw [← X_pow_eq_monomial, ← X_pow_eq_monomial]
  simp [add_comm]

theorem countingPolynomial_power (k : ℕ) :
    countingPolynomial ι ^ k =
      ∑ t : Fin k → ι × Bool, monomial (tupleExponent k t) 1 := by
  classical
  rw [countingPolynomial_atom_sum, Fintype.sum_pow]
  exact Finset.sum_congr rfl fun t _ => (monomial_sum_one Finset.univ (fun j => atomExponent (t j))).symm

/-- The coefficient counts every ordered tuple with the given exponent vector. -/
theorem coefficient_eq_tuple_count (k : ℕ) (d : ι →₀ ℕ) :
    coeff d (countingPolynomial ι ^ k) = exponentMultiplicity k d := by
  classical
  rw [countingPolynomial_power, coeff_sum, exponentMultiplicity]
  simp only [coeff_monomial, Finset.sum_boole, Nat.cast_id]

theorem tupleExponent_weight (k : ℕ) (t : Fin k → ι × Bool) :
    exponentWeight (tupleExponent k t) = k + squareCount k t := by
  classical
  unfold exponentWeight tupleExponent
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  have he (a : ι × Bool) : (∑ i, atomExponent a i) = 1 + if a.2 = true then 1 else 0 := by
    simp only [atomExponent, Finsupp.single_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    cases a.2 <;> norm_num
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id, squareCount]

/-- The derivative bound gives a factor two for each square choice. -/
theorem tuple_count_le_factorial_two (k : ℕ) (t : Fin k → ι × Bool) :
    exponentMultiplicity k (tupleExponent k t) ≤
      k.factorial * 2 ^ squareCount k t := by
  have h := coefficient_factorial_bound k (tupleExponent k t)
  rw [coefficient_eq_tuple_count, tupleExponent_weight, pow_add] at h
  have h' :
      exponentMultiplicity k (tupleExponent k t) *
        2 ^ k ≤ (k.factorial * 2 ^ squareCount k t) * 2 ^ k := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < (2 : ℕ) ^ k)).mp
    (by simpa only [mul_comm] using h')

theorem tuple_count_le_factorial_four (k : ℕ) (t : Fin k → ι × Bool) :
    exponentMultiplicity k (tupleExponent k t) ≤
      k.factorial * 4 ^ squareCount k t :=
  (tuple_count_le_factorial_two k t).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2 ≤ 4) _))

end NField.Alignment.HarperTuplePolynomial
