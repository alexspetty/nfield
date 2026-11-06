/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliStraightening

/-! # The published all-base carry representation

The older straightening proof carried a prime hypothesis that its finite
arithmetic does not use. This extension keeps the same floor count and
straightening unit, and proves the literal statement for every base at least
two, including every nonunit sample.
-/

namespace NField.Alignment.CommonResetCarry

open scoped BigOperators ZMod
open CarryBoundarySpectra CollisionFluctuationSum PrimeCarryTableColumnLaw
open CollisionBernoulliStraightening

noncomputable def fractionalResponse
    {p : ℕ} (hp : 2 ≤ p) (a : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  exact ∑ d ∈ Finset.range p,
    (residueFraction (collisionPoint p d * a) -
      residueFraction (collisionPointNext p d * a))

/-- The straightened finite Bernoulli boundary. -/
noncomputable def bernoulliBoundary
    {p : ℕ} (_hp : 2 ≤ p) (a : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  exact 2 * ∑ r ∈ Finset.Ico 1 p,
    centeredSawtooth (((r : ℕ) : ZMod (p ^ 2)) * a)


theorem collisionResponse_eq_fractionalResponse
    {p : ℕ} (hp : 2 ≤ p) (a : ZMod (p ^ 2)) :
    collisionResponse p a = fractionalResponse hp a := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  have hp2pos : 0 < p ^ 2 := pow_pos (by omega : 0 < p) 2
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp2ℂ : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (by omega : p ≠ 0))
  have hpoint (d : ℕ) (_hd : d ∈ Finset.range p) :
      (floorJump (p ^ 2) a.val ((p + 1) * d) : ℂ) =
        (a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ) +
          (residueFraction
              (collisionPoint p d * a) -
            residueFraction
              (collisionPointNext p d * a)) := by
    rw [floorJump_eq_fractionalDifference hp2pos]
    simp only [residueFraction, collisionPoint, collisionPointNext,
      ZMod.val_mul, ZMod.val_natCast]
    congr 2 <;> rw [Nat.mul_mod] <;>
      simp only [Nat.mod_eq_of_lt a.val_lt]
  unfold collisionResponse fractionalResponse carryThresholdCount
  have hcast :
      ((∑ d ∈ Finset.range p,
          floorJump (p ^ 2) a.val ((p + 1) * d) : ℤ) : ℂ) =
        ∑ d ∈ Finset.range p,
          (floorJump (p ^ 2) a.val ((p + 1) * d) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  rw [show (∑ _d ∈ Finset.range p,
      (a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ)) =
        (p : ℂ) * ((a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ)) by simp]
  field_simp [hpℂ, hp2ℂ]
  ring


theorem fractional_to_bernoulli_straightening
    {p : ℕ} (hp : 2 ≤ p) (A : ZMod (p ^ 2)) :
    fractionalResponse hp ((straighteningUnit p).val * A) =
      bernoulliBoundary hp A := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  have hp2 : 2 ≤ p ^ 2 := by nlinarith [hp]
  have hbase :
      ((p + 1 : ℕ) : ZMod (p ^ 2)) * (straighteningUnit p).val = 1 := by
    change ((p + 1 : ℕ) : ZMod (p ^ 2)) * (1 - p) = 1
    have hp2zero : (p : ZMod (p ^ 2)) * p = 0 := by
      rw [← Nat.cast_mul, show p * p = p ^ 2 by ring, ZMod.natCast_self]
    push_cast
    linear_combination -hp2zero
  have hpoint (d : ℕ) (hd : d ∈ Finset.range p) :
      residueFraction
          ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A)) -
        residueFraction
          (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A))) =
      residueFraction (((d : ℕ) : ZMod (p ^ 2)) * A) -
        residueFraction
          (-(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A)) := by
    have hdlt : d < p := Finset.mem_range.mp hd
    have hfirst :
        ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A)) =
          ((d : ℕ) : ZMod (p ^ 2)) * A := by
      rw [show (((p + 1) * d : ℕ) : ZMod (p ^ 2)) =
          ((p + 1 : ℕ) : ZMod (p ^ 2)) * (d : ZMod (p ^ 2)) by
        push_cast
        rfl]
      calc
        (((p + 1 : ℕ) : ZMod (p ^ 2)) * d) *
            ((straighteningUnit p).val * A) =
            (d : ZMod (p ^ 2)) *
              ((((p + 1 : ℕ) : ZMod (p ^ 2)) *
                (straighteningUnit p).val) * A) := by ring
        _ = (d : ZMod (p ^ 2)) * A := by rw [hbase, one_mul]
    have hsecondCoeff :
        ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) =
          -((p - 1 - d : ℕ) : ZMod (p ^ 2)) := by
      calc
        ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) =
            ((((p + 1 : ℕ) : ZMod (p ^ 2)) * d + 1) *
              (straighteningUnit p).val) := by
                congr 1
                push_cast
                rfl
        _ = (d : ZMod (p ^ 2)) *
              (((p + 1 : ℕ) : ZMod (p ^ 2)) *
                (straighteningUnit p).val) + (straighteningUnit p).val := by ring
        _ = (d : ZMod (p ^ 2)) + (straighteningUnit p).val := by rw [hbase, mul_one]
        _ = -((p - 1 - d : ℕ) : ZMod (p ^ 2)) := by
          change (d : ZMod (p ^ 2)) + (1 - p) = _
          have hnat : d + (p - 1 - d) = p - 1 := by omega
          have hcast := congrArg
            (fun n : ℕ => (n : ZMod (p ^ 2))) hnat
          rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p)] at hcast
          linear_combination hcast
    rw [hfirst]
    congr 1
    apply congrArg residueFraction
    calc
      (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
          ((straighteningUnit p).val * A))) =
          (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) * A) := by ring
      _ = -(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A) := by
        rw [hsecondCoeff]
        ring
  unfold fractionalResponse bernoulliBoundary
  simp only [collisionPoint, collisionPointNext]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hreflect := Finset.sum_range_reflect
    (fun d : ℕ => residueFraction
      (-(((d : ℕ) : ZMod (p ^ 2)) * A))) p
  have hsecond :
      (∑ d ∈ Finset.range p,
          residueFraction (-(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A))) =
        ∑ d ∈ Finset.range p,
          residueFraction (-(((d : ℕ) : ZMod (p ^ 2)) * A)) := by
    simpa using hreflect
  rw [hsecond, ← Finset.sum_sub_distrib]
  have hpair (d : ℕ) (_hd : d ∈ Finset.range p) :
      residueFraction (((d : ℕ) : ZMod (p ^ 2)) * A) -
          residueFraction (-(((d : ℕ) : ZMod (p ^ 2)) * A)) =
        2 * centeredSawtooth (((d : ℕ) : ZMod (p ^ 2)) * A) :=
    residueFraction_sub_neg hp2 _
  rw [Finset.sum_congr rfl hpair]
  rw [show Finset.range p = insert 0 (Finset.Ico 1 p) by
    have hp0 := (by omega : 0 < p)
    ext d
    simp
    omega]
  rw [Finset.sum_insert (by simp)]
  simp [Finset.mul_sum, centeredSawtooth]

/-- Title: `Carry representation in every integer base`. -/
theorem collision_to_bernoulli_straightening
    {p : ℕ} (hp : 2 ≤ p) (A : ZMod (p ^ 2)) :
    collisionResponse p ((straighteningUnit p).val * A) =
      bernoulliBoundary hp A := by
  rw [collisionResponse_eq_fractionalResponse hp,
    fractional_to_bernoulli_straightening hp]

/-- The finite square energy before straightening. -/
noncomputable def collisionEnergy {p : ℕ} (hp : 2 ≤ p) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  exact ∑ a : ZMod (p ^ 2), ‖collisionResponse p a‖ ^ 2

/-- The finite Bernoulli square energy after straightening. -/
noncomputable def bernoulliEnergy {p : ℕ} (hp : 2 ≤ p) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  exact ∑ A : ZMod (p ^ 2), ‖bernoulliBoundary hp A‖ ^ 2

/-- Title: `Carry energy equals sampled clock energy in every base`. -/
theorem collision_energy_eq_bernoulli_energy
    {p : ℕ} (hp : 2 ≤ p) : collisionEnergy hp = bernoulliEnergy hp := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega : p ≠ 0)⟩
  unfold collisionEnergy bernoulliEnergy
  let e : ZMod (p ^ 2) ≃ ZMod (p ^ 2) := (straighteningUnit p).mulLeft
  have hreindex := e.sum_comp (fun a : ZMod (p ^ 2) => ‖collisionResponse p a‖ ^ 2)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro A _
  change ‖collisionResponse p ((straighteningUnit p).val * A)‖ ^ 2 = _
  rw [collision_to_bernoulli_straightening hp]


end NField.Alignment.CommonResetCarry
