/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartitionTaylor
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The actual Taylor product as a polynomial in values and conjugates

The two variable families retain every occurrence on each side of a
character pairing. The total degree is derived from the constructed Taylor
polynomials, rather than assumed as a property of an expansion.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators
open MvPolynomial

namespace NField.Alignment.HarperTaylorExpansion

variable {ι : Type*} [Fintype ι]

def values (z : ι → ℂ) : Bool × ι → ℂ :=
  fun v => if v.1 then z v.2 else star (z v.2)

def realArgument (c z : ι → ℂ) : ℝ := (∑ i, c i*z i).re

def linear (c : ι → ℂ) : MvPolynomial (Bool × ι) ℂ :=
  ∑ i, (C (c i/2)*X (true,i) + C (star (c i)/2)*X (false,i))

theorem linear_eval (c z : ι → ℂ) :
    eval (values z) (linear c) = (realArgument c z : ℂ) := by
  classical
  simp only [linear, map_sum, map_add, map_mul, eval_C, eval_X, values,
    ↓reduceIte, realArgument]
  rw [Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem linear_degree (c : ι → ℂ) : (linear c).totalDegree ≤ 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_add _ _).trans
  apply max_le
  · simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C (c i/2)) (X (true,i))
  · simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C (star (c i)/2)) (X (false,i))

def taylor (delta : ℝ) (J : ℕ) (label : Fin (2*J+2)) (N : ℕ)
    (c : ι → ℂ) : MvPolynomial (Bool × ι) ℂ :=
  ∑ k ∈ Finset.range N,
    C ((HarperPartitionTaylor.polynomial delta J label N).coeff k : ℂ) * (linear c)^k

theorem taylor_eval (delta : ℝ) (J : ℕ) (label : Fin (2*J+2)) (N : ℕ)
    (c z : ι → ℂ) : eval (values z) (taylor delta J label N c) =
      ((Polynomial.eval (realArgument c z)
        (HarperPartitionTaylor.polynomial delta J label N) : ℝ) : ℂ) := by
  classical
  rw [HarperPartitionTaylor.polynomial_eval]
  simp only [taylor, map_sum, map_mul, eval_C, map_pow, linear_eval, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [HarperPartitionTaylor.polynomial_coeff, if_pos (Finset.mem_range.mp hk)]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

theorem taylor_degree (delta : ℝ) (J : ℕ) (label : Fin (2*J+2)) (N : ℕ)
    (c : ι → ℂ) : (taylor delta J label N c).totalDegree ≤ N-1 := by
  classical
  apply totalDegree_finsetSum_le
  intro k hk
  calc
    _ ≤ (C ((HarperPartitionTaylor.polynomial delta J label N).coeff k : ℂ)).totalDegree +
        ((linear c)^k).totalDegree := totalDegree_mul _ _
    _ ≤ k := by
      simp only [totalDegree_C, zero_add]
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left k (linear_degree c))
    _ ≤ N-1 := by have := Finset.mem_range.mp hk; omega

def product (delta : ℝ) (J N A : ℕ) (labels : Fin A → Fin (2*J+2))
    (c : Fin A → ι → ℂ) : MvPolynomial (Bool × ι) ℂ :=
  ∏ j, taylor delta J (labels j) N (c j)

theorem product_eval (delta : ℝ) (J N A : ℕ) (labels : Fin A → Fin (2*J+2))
    (c : Fin A → ι → ℂ) (z : ι → ℂ) :
    eval (values z) (product delta J N A labels c) =
      ((∏ j, (HarperPartitionTaylor.polynomial delta J (labels j) N).eval
        (realArgument (c j) z)) : ℝ) := by
  simp only [product, map_prod, taylor_eval, Complex.ofReal_prod]

theorem product_degree (delta : ℝ) (J N A : ℕ) (labels : Fin A → Fin (2*J+2))
    (c : Fin A → ι → ℂ) : (product delta J N A labels c).totalDegree ≤ A*(N-1) := by
  calc
    _ ≤ ∑ j : Fin A, (taylor delta J (labels j) N (c j)).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _j : Fin A, (N-1) := Finset.sum_le_sum fun j _ => taylor_degree delta J (labels j) N (c j)
    _ = _ := by simp

def sideCount (d : (Bool × ι) →₀ ℕ) (b : Bool) : ℕ := ∑ i, d (b,i)

def sideIndex (a : ι → ℕ) (d : (Bool × ι) →₀ ℕ) (b : Bool) : ℕ :=
  ∏ i, (a i)^d (b,i)

def occurrences (d : (Bool × ι) →₀ ℕ) (b : Bool) : Finset (Σ _ : ι, ℕ) :=
  Finset.univ.sigma fun i => Finset.range (d (b,i))

theorem occurrences_card (d : (Bool × ι) →₀ ℕ) (b : Bool) :
    (occurrences d b).card = sideCount d b := by
  simp [occurrences, Finset.card_sigma, sideCount]

theorem occurrences_product (a : ι → ℕ) (d : (Bool × ι) →₀ ℕ) (b : Bool) :
    (∏ v ∈ occurrences d b, a v.1) = sideIndex a d b := by
  simp [occurrences, Finset.prod_sigma, sideIndex]

theorem sideCount_le {Q : MvPolynomial (Bool × ι) ℂ}
    {d : (Bool × ι) →₀ ℕ} (hd : d ∈ Q.support) (b : Bool) :
    sideCount d b ≤ Q.totalDegree := by
  apply le_trans _ (le_totalDegree hd)
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

theorem product_occurrences (delta : ℝ) (J N A : ℕ) (labels : Fin A → Fin (2*J+2))
    (c : Fin A → ι → ℂ) {d : (Bool × ι) →₀ ℕ}
    (hd : d ∈ (product delta J N A labels c).support) (b : Bool) :
    sideCount d b ≤ A*(N-1) :=
  (sideCount_le hd b).trans (product_degree delta J N A labels c)

/-- A monomial evaluates to the two complete integer products, with every
exponent and its conjugation direction retained. -/
theorem monomial_pair (a : ι → ℕ) (d : (Bool × ι) →₀ ℕ) (z : ℕ →* ℂ) :
    (∏ v, (values (fun i => z (a i)) v)^d v) =
      z (sideIndex a d true) * star (z (sideIndex a d false)) := by
  classical
  rw [Fintype.prod_prod_type]
  simp [values, sideIndex, map_prod, map_pow]

theorem evaluation_expansion (Q : MvPolynomial (Bool × ι) ℂ)
    (a : ι → ℕ) (z : ℕ →* ℂ) :
    eval (values (fun i => z (a i))) Q =
      ∑ d ∈ Q.support, Q.coeff d *
        (z (sideIndex a d true) * star (z (sideIndex a d false))) := by
  rw [eval_eq']
  simp_rw [monomial_pair]

end NField.Alignment.HarperTaylorExpansion
