/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteResolutionCurrent

/-!
# Reciprocal increments and the von Mangoldt current

Division by the address preserves Dirichlet convolution. Thus Mathlib's
classical Möbius identities give the exact reciprocal inverse and current.
-/

noncomputable section

namespace NField.Alignment.ReciprocalResolutionCurrent

open scoped BigOperators ArithmeticFunction
open FiniteResolutionCurrent

def reciprocalTwist (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / (n : ℝ), by simp⟩

@[simp] theorem reciprocal_twist_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    reciprocalTwist f n = f n / (n : ℝ) := rfl

theorem reciprocal_twist_mul (f g : ArithmeticFunction ℝ) :
    reciprocalTwist (f * g) = reciprocalTwist f * reciprocalTwist g := by
  ext n
  simp only [reciprocal_twist_apply, ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hmul, Nat.cast_mul]
  exact div_mul_div_comm (f p.1) (p.1 : ℝ) (g p.2) (p.2 : ℝ) |>.symm

@[simp] theorem reciprocal_twist_one : reciprocalTwist 1 = 1 := by
  ext n
  by_cases hn : n = 1 <;> simp [reciprocalTwist, ArithmeticFunction.one_apply, hn]

def reciprocalSequence : ArithmeticFunction ℝ :=
  reciprocalTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

@[simp] theorem reciprocal_sequence_apply (n : ℕ) :
    reciprocalSequence n = 1 / (n : ℝ) := by
  by_cases hn : n = 0 <;>
    simp [reciprocalSequence, reciprocalTwist, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hn]

@[simp] theorem reciprocal_sequence_one : reciprocalSequence 1 = 1 := by simp

/-- Title: `Möbius inversion of the reciprocal sequence`. -/
theorem reciprocal_moebius_inverse :
    ArithmeticFunction.dirichletInverse reciprocalSequence
      (normalizedInvertible reciprocalSequence reciprocal_sequence_one) =
      reciprocalTwist (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  have ht : reciprocalSequence *
      reciprocalTwist (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
    rw [reciprocalSequence, ← reciprocal_twist_mul,
      ArithmeticFunction.coe_zeta_mul_coe_moebius, reciprocal_twist_one]
  let inv := ArithmeticFunction.dirichletInverse reciprocalSequence
    (normalizedInvertible reciprocalSequence reciprocal_sequence_one)
  have hi : inv * reciprocalSequence = 1 :=
    ArithmeticFunction.dirichletInverse_mul_self _ _
  change inv = _
  calc
    inv = inv * 1 := (mul_one inv).symm
    _ = inv * (reciprocalSequence *
        reciprocalTwist (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by rw [ht]
    _ = (inv * reciprocalSequence) *
        reciprocalTwist (ArithmeticFunction.moebius : ArithmeticFunction ℝ) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [hi, one_mul]

/-- Title: `The reciprocal sequence has inverse coefficient Möbius over the address`. -/
theorem reciprocal_inverse_apply (n : ℕ) :
    ArithmeticFunction.dirichletInverse reciprocalSequence
      (normalizedInvertible reciprocalSequence reciprocal_sequence_one) n =
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  rw [reciprocal_moebius_inverse]
  rfl

theorem reciprocal_log_mark :
    logMark reciprocalSequence = reciprocalTwist ArithmeticFunction.log := by
  ext n
  simp only [log_mark_apply, reciprocal_sequence_apply, reciprocal_twist_apply,
    ArithmeticFunction.log_apply]
  ring

/-- Title: `The reciprocal current coefficient is von Mangoldt over the address`. -/
theorem reciprocal_current_coefficient :
    currentCoefficient reciprocalSequence reciprocal_sequence_one =
      reciprocalTwist ArithmeticFunction.vonMangoldt := by
  unfold currentCoefficient
  rw [reciprocal_moebius_inverse, reciprocal_log_mark, ← reciprocal_twist_mul,
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt]

/-- Title: `The reciprocal sequence has the von Mangoldt current`.

 Every address, including all prime powers, has the classical coefficient. -/
theorem reciprocal_current_eq_von_mangoldt (n : ℕ) :
    signedCurrent reciprocalSequence reciprocal_sequence_one n =
      ArithmeticFunction.vonMangoldt n := by
  unfold signedCurrent
  rw [reciprocal_current_coefficient, reciprocal_twist_apply]
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Title: `The reciprocal current records the logarithm at each prime power`. -/
theorem reciprocal_current_prime_power {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    signedCurrent reciprocalSequence reciprocal_sequence_one (p ^ j) = Real.log (p : ℝ) := by
  rw [reciprocal_current_eq_von_mangoldt, ArithmeticFunction.vonMangoldt_apply_pow hj,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Title: `The reciprocal current vanishes exactly away from prime powers`. -/
theorem reciprocal_current_zero_iff (n : ℕ) :
    signedCurrent reciprocalSequence reciprocal_sequence_one n = 0 ↔ ¬IsPrimePow n := by
  rw [reciprocal_current_eq_von_mangoldt, ArithmeticFunction.vonMangoldt_eq_zero_iff]

/-- Title: `The von Mangoldt current recognizes the reciprocal sequence`. -/
theorem von_mangoldt_current_recognizes_reciprocal_sequence
    (a : ArithmeticFunction ℝ) (ha : a 1 = 1) :
    (∀ n, signedCurrent a ha n = ArithmeticFunction.vonMangoldt n) ↔
      a = reciprocalSequence := by
  constructor
  · intro h
    apply signed_current_injective a reciprocalSequence ha reciprocal_sequence_one
    intro n
    rw [h n, reciprocal_current_eq_von_mangoldt]
  · rintro rfl
    exact reciprocal_current_eq_von_mangoldt

end NField.Alignment.ReciprocalResolutionCurrent
