/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Finite reconstruction from the signed resolution current

The normalized increment sequence is recovered by finite Dirichlet algebra.
Mathlib supplies the convolution inverse and the von Mangoldt identity.
-/

noncomputable section

namespace NField.Alignment.FiniteResolutionCurrent

open scoped BigOperators

def logMark (a : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => a n * Real.log (n : ℝ), by simp⟩

@[reducible] def normalizedInvertible (a : ArithmeticFunction ℝ) (ha : a 1 = 1) :
    Invertible (a 1) where
  invOf := 1
  invOf_mul_self := by simp [ha]
  mul_invOf_self := by simp [ha]

def currentCoefficient (a : ArithmeticFunction ℝ) (ha : a 1 = 1) :
    ArithmeticFunction ℝ :=
  logMark a * ArithmeticFunction.dirichletInverse a (normalizedInvertible a ha)

def signedCurrent (a : ArithmeticFunction ℝ) (ha : a 1 = 1) (n : ℕ) : ℝ :=
  (n : ℝ) * currentCoefficient a ha n

@[simp] theorem log_mark_apply (a : ArithmeticFunction ℝ) (n : ℕ) :
    logMark a n = a n * Real.log (n : ℝ) := rfl

@[simp] theorem current_coefficient_one (a : ArithmeticFunction ℝ) (ha : a 1 = 1) :
    currentCoefficient a ha 1 = 0 := by
  simp [currentCoefficient, logMark]

@[simp] theorem signed_current_one (a : ArithmeticFunction ℝ) (ha : a 1 = 1) :
    signedCurrent a ha 1 = 0 := by
  simp [signedCurrent]

/-- Title: `Convolution with the increment sequence recovers logarithmic marking`. -/
theorem current_coefficient_times_sequence (a : ArithmeticFunction ℝ)
    (ha : a 1 = 1) : currentCoefficient a ha * a = logMark a := by
  rw [currentCoefficient, mul_assoc, ArithmeticFunction.dirichletInverse_mul_self, mul_one]

/-- Title: `Dividing the signed current by its address recovers its coefficient`. -/
theorem current_div_address (a : ArithmeticFunction ℝ) (ha : a 1 = 1) (n : ℕ) :
    signedCurrent a ha n / (n : ℝ) = currentCoefficient a ha n := by
  by_cases hn : n = 0
  · simp [hn, signedCurrent]
  · unfold signedCurrent
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Title: `Exact divisor reconstruction from the signed current`. -/
theorem current_reconstruction_sum (a : ArithmeticFunction ℝ) (ha : a 1 = 1)
    (n : ℕ) :
    ∑ d ∈ n.divisors, signedCurrent a ha d / (d : ℝ) * a (n / d) =
      a n * Real.log (n : ℝ) := by
  simp_rw [current_div_address]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (current_coefficient_times_sequence a ha)
  simpa only [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d k => currentCoefficient a ha d * a k),
    log_mark_apply] using h

/-- Title: `Triangular reconstruction of the normalized increment sequence`.

 The manuscript's triangular recursion, with only smaller arguments on the right. -/
theorem triangular_current_inverse (a : ArithmeticFunction ℝ) (ha : a 1 = 1)
    {n : ℕ} (hn : 2 ≤ n) :
    a n = (1 / Real.log (n : ℝ)) *
      ∑ d ∈ n.divisors with 1 < d,
        signedCurrent a ha d / (d : ℝ) * a (n / d) := by
  have hs : (∑ d ∈ n.divisors with 1 < d,
      signedCurrent a ha d / (d : ℝ) * a (n / d)) =
      ∑ d ∈ n.divisors, signedCurrent a ha d / (d : ℝ) * a (n / d) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hd1 : d = 1 := by
      have hpos := Nat.pos_of_mem_divisors hd
      simp only [Finset.mem_filter, hd, true_and, not_lt] at hnot
      omega
    simp [hd1]
  rw [hs, current_reconstruction_sum]
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  field_simp

/-- Title: `The signed current determines the normalized increment sequence`.

 The normalized increment sequence is determined at every address. -/
theorem signed_current_injective (a b : ArithmeticFunction ℝ)
    (ha : a 1 = 1) (hb : b 1 = 1)
    (hcurrent : ∀ n, signedCurrent a ha n = signedCurrent b hb n) : a = b := by
  apply ArithmeticFunction.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simp [hn0]
      by_cases hn1 : n = 1
      · simp [hn1, ha, hb]
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hsum : (∑ d ∈ n.divisors,
          signedCurrent a ha d / (d : ℝ) * a (n / d)) =
          ∑ d ∈ n.divisors, signedCurrent b hb d / (d : ℝ) * b (n / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [hcurrent]
        by_cases hd1 : d = 1
        · simp [hd1]
        · have hd2 : 1 < d := by
            have := Nat.pos_of_mem_divisors hd
            omega
          rw [ih (n / d) (Nat.div_lt_self hn hd2)]
      rw [current_reconstruction_sum, current_reconstruction_sum] at hsum
      have hlog : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      exact mul_right_cancel₀ hlog hsum

end NField.Alignment.FiniteResolutionCurrent
