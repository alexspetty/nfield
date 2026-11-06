/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteResolutionMass

/-!
# Recognition of the actual collision mass by its signed current

The existing collision harmonic-seed identity supplies the literal rows.
The general current reconstruction then gives mass recognition.
-/

noncomputable section

namespace NField.Alignment.CollisionResolutionCurrent

open scoped BigOperators
open FiniteResolutionMass FiniteResolutionCurrent ReciprocalResolutionCurrent
open CollisionRemainderDynamics CollisionAmplitudeArithmetic CollisionMassReadout

/-- Title: `The collision unprimitive row is the harmonic seed`. -/
theorem collision_unprimitive_row {n : ℕ} (hn : 0 < n) :
    unprimitiveRow collisionWeight n = harmonicKernel n :=
  (harmonicKernel_divisor n hn).symm

/-- Title: `The collision row potential is the preceding harmonic number`. -/
theorem collision_row_potential (n : ℕ) :
    rowPotential collisionWeight n = (harmonic (n - 1) : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [rowPotential, collision_unprimitive_row (Nat.pos_of_ne_zero hn), harmonicKernel]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- Title: `The collision resolution increment is the reciprocal address`. -/
theorem collision_resolution_increment {n : ℕ} (hn : 0 < n) :
    resolutionIncrement collisionWeight n = 1 / (n : ℝ) := by
  unfold resolutionIncrement
  rw [collision_row_potential, collision_row_potential]
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hh := congrArg (fun x : ℚ => (x : ℝ)) (harmonic_succ (n - 1))
  simp only [hn', Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hh
  simp only [Nat.add_sub_cancel]
  rw [hh]
  ring

/-- Title: `The normalized collision increments form the reciprocal sequence`. -/
theorem collision_normalized_sequence : normalizedSequence collisionWeight = reciprocalSequence := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [normalized_sequence_apply _ (Nat.pos_of_ne_zero hn),
    collision_resolution_increment (Nat.pos_of_ne_zero hn), collisionWeight_two,
    reciprocal_sequence_apply]
  norm_num

/-- Title: `The collision mass has the von Mangoldt current`. -/
theorem collision_mass_current (n : ℕ) :
    massCurrent collisionWeight (by simp) (by rw [collisionWeight_two]; norm_num) n =
      ArithmeticFunction.vonMangoldt n := by
  unfold massCurrent
  simpa only [collision_normalized_sequence] using reciprocal_current_eq_von_mangoldt n

/-- Title: `The von Mangoldt current recognizes the collision mass`.

 Complete current equality recognizes any normalized mass with positive second mass. -/
theorem von_mangoldt_current_recognizes_collision_mass (v : ℕ → ℝ)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 ≠ 0)
    (hvMass : ∑' k, v k = 1) :
    (∀ n, massCurrent v hv1 hv2 n = ArithmeticFunction.vonMangoldt n) ↔
      v = collisionWeight := by
  constructor
  · intro hc
    apply mass_current_injective v collisionWeight hv0 (by simp) hv1 (by simp) hv2
      (by rw [collisionWeight_two]; norm_num) hvMass collisionWeight_tsum
    intro n
    rw [hc n, collision_mass_current]
  · rintro rfl
    exact collision_mass_current

/-- Title: `The collision current records the logarithm at each prime power`. -/
theorem collision_mass_current_prime_power {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    massCurrent collisionWeight (by simp) (by rw [collisionWeight_two]; norm_num) (p ^ j) =
      Real.log (p : ℝ) := by
  rw [collision_mass_current, ArithmeticFunction.vonMangoldt_apply_pow hj,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

end NField.Alignment.CollisionResolutionCurrent
