/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicLValue
import NField.Alignment.CollisionDirichletBoundary
import NField.Alignment.OddBernoulliPrimeSquare
import Mathlib.Algebra.Ring.Periodic

/-!
# Uniform truncation of the actual character L-value at one

A complete period of a nonprincipal character has sum zero. Every shifted
partial sum is therefore bounded by the modulus. Finite Abel summation and
the proved ordered endpoint identify the tail with the actual continued
Dirichlet L-function, without using absolute convergence at one.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeLTruncation

open scoped BigOperators Topology ZMod
open Filter
open NField.Alignment.CollisionPeriodicLValue
open NField.Alignment.CollisionDirichletBoundary
open NField.Alignment.OddBernoulliMoments
open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.PrimeCarrySpectralBridge

variable {q : ℕ} [NeZero q]

theorem shifted_period_sum (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (r : ℕ) :
    (∑ i ∈ Finset.range q, χ ((r+i+1 : ℕ) : ZMod q)) = 0 := by
  rw [← sum_zmod_val (fun i => χ ((r+i+1 : ℕ) : ZMod q))]
  have h := Equiv.sum_comp (Equiv.addLeft ((r+1 : ℕ) : ZMod q))
    (fun x : ZMod q => χ x)
  rw [χ.sum_eq_zero_of_ne_one hχ] at h
  simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h

theorem shifted_character_sum_mod (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (r T : ℕ) :
    (∑ i ∈ Finset.range T, χ ((r+i+1 : ℕ) : ZMod q)) =
      ∑ i ∈ Finset.range (T%q), χ ((r+i+1 : ℕ) : ZMod q) := by
  let S : ℕ → ℂ := fun n => ∑ i ∈ Finset.range n, χ ((r+i+1 : ℕ) : ZMod q)
  have hperiod : Function.Periodic S q := by
    intro n
    dsimp [S]
    rw [Finset.sum_range_add]
    have hp : (∑ i ∈ Finset.range q, χ ((r+(n+i)+1 : ℕ) : ZMod q)) = 0 := by
      simpa [Nat.add_assoc] using shifted_period_sum χ hχ (r+n)
    rw [hp, add_zero]
  have h := hperiod.nat_mul (T/q) (T%q)
  simpa only [Nat.cast_id, Nat.mul_comm (T/q) q, Nat.mod_add_div] using h

theorem shifted_character_sum_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (r T : ℕ) :
    ‖∑ i ∈ Finset.range T, χ ((r+i+1 : ℕ) : ZMod q)‖ ≤ (q : ℝ) := by
  rw [shifted_character_sum_mod χ hχ]
  calc
    _ ≤ ∑ i ∈ Finset.range (T%q), ‖χ ((r+i+1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T%q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact χ.norm_le_one _
    _ ≤ q := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast (Nat.mod_lt T (NeZero.pos q)).le

theorem character_partial_sum_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (T : ℕ) :
    ‖∑ i ∈ Finset.range T, χ ((i+1 : ℕ) : ZMod q)‖ ≤ (q : ℝ) := by
  simpa only [Nat.zero_add] using shifted_character_sum_bound χ hχ 0 T

theorem positive_interval_sum_eq_range (f : ℕ → ℂ) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, f n) = ∑ i ∈ Finset.range T, f (i+1) := by
  induction T with
  | zero => simp
  | succ T hT =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, hT]

/-- The printed partial-sum bound, with the real cutoff interpreted by its
natural floor and the positive-integer interval kept explicit. -/
theorem character_real_partial_sum_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  rw [positive_interval_sum_eq_range]
  exact character_partial_sum_bound χ hχ _

theorem ordered_partial_difference (χ : DirichletCharacter ℂ q) (T N : ℕ) :
    orderedLPartial χ (T+N) - orderedLPartial χ T =
      ∑ i ∈ Finset.range N, χ ((T+i+1 : ℕ) : ZMod q) / ((T+i+1 : ℕ) : ℂ) := by
  unfold orderedLPartial
  rw [Finset.sum_range_add, add_sub_cancel_left]

theorem ordered_partial_tail_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (T N : ℕ) :
    ‖orderedLPartial χ (T+N) - orderedLPartial χ T‖ ≤ (q : ℝ)/(T+1) := by
  rw [ordered_partial_difference]
  have h := norm_sum_range_smul_le
    (f := fun i => (1 : ℝ)/((T+i+1 : ℕ) : ℝ))
    (z := fun i => χ ((T+i+1 : ℕ) : ZMod q)) (C := (q : ℝ))
    (fun _ => by positivity) (by
      intro i j hij
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hij T) 1)
    (fun n => shifted_character_sum_bound χ hχ T n) N
  simpa [Complex.real_smul, div_eq_mul_inv, mul_comm] using h

/-- A bound stronger than the manuscript's `2q/T`, valid even at `T=0`. -/
theorem l_one_tail_bound_succ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (T : ℕ) :
    ‖DirichletCharacter.LFunction χ 1 - orderedLPartial χ T‖ ≤ (q : ℝ)/(T+1) := by
  have hL : Tendsto (orderedLPartial χ) atTop (𝓝 (DirichletCharacter.LFunction χ 1)) :=
    orderedLPartial_tendsto χ (χ.sum_eq_zero_of_ne_one hχ)
  have ht := ((hL.comp (tendsto_add_atTop_nat T)).sub_const (orderedLPartial χ T)).norm
  apply le_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => by
    change ‖orderedLPartial χ (n+T) - orderedLPartial χ T‖ ≤ _
    rw [Nat.add_comm n T]
    exact ordered_partial_tail_bound χ hχ T n

/-- The printed uniform tail estimate after a positive integer cutoff. -/
theorem l_one_tail_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {T : ℕ} (hT : 0 < T) :
    ‖DirichletCharacter.LFunction χ 1 - orderedLPartial χ T‖ ≤ 2*(q : ℝ)/T := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    _ ≤ (q : ℝ)/(T+1) := l_one_tail_bound_succ χ hχ T
    _ ≤ (q : ℝ)/T := by gcongr; linarith
    _ ≤ 2*(q : ℝ)/T := by gcongr; nlinarith [Nat.cast_nonneg (α := ℝ) q]

theorem l_one_modulus_square_truncation (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1 - orderedLPartial χ (q^2)‖ ≤ 2/(q : ℝ) := by
  have h := l_one_tail_bound χ hχ (pow_pos (NeZero.pos q) 2)
  rw [Nat.cast_pow] at h
  calc
    _ ≤ 2*(q : ℝ)/(q : ℝ)^2 := h
    _ = _ := by field_simp

theorem l_one_interval_truncation (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1 -
      ∑ n ∈ Finset.Icc 1 (q^2), χ (n : ZMod q)/(n : ℂ)‖ ≤ 2/(q : ℝ) := by
  rw [positive_interval_sum_eq_range]
  exact l_one_modulus_square_truncation χ hχ

/-- The exact prime-square truncation used in Proposition 10. -/
theorem primitive_odd_l_truncation {p : ℕ} [NeZero (p^2)]
    (χ : PrimitiveOddFamily p) :
    ‖DirichletCharacter.LFunction χ.val 1 - orderedLPartial χ.val (p^4)‖ ≤
      2/(p : ℝ)^2 := by
  have h := l_one_modulus_square_truncation χ.val (odd_character_ne_one χ.val χ.property.2)
  simpa only [← pow_mul, Nat.reduceMul, Nat.cast_pow] using h

end NField.Alignment.MagnitudeLTruncation
