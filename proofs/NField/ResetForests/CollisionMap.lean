/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.NonunitGram
/-! # The literal threshold table and its complete source Gram -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.GramDecomposition

open scoped BigOperators Matrix
open NField.Alignment CommonResetGram CommonResetGrid CommonResetSampling
open CollisionRampEnergy CollisionFluctuationSum PrimeCarryTableColumnLaw
open CollisionBernoulliStraightening SourceMetrics FibreReconstruction

def thresholdCount (p a : ℕ) : ℤ :=
  ∑ d ∈ Finset.range p,
    (⌊((((p+1)*d+1)*a : ℕ) : ℝ)/((p^2 : ℕ) : ℝ)⌋-
      ⌊((((p+1)*d)*a : ℕ) : ℝ)/((p^2 : ℕ) : ℝ)⌋)

theorem literal_threshold_count (p a : ℕ) : thresholdCount p a=carryThresholdCount p a := by
  simp only [thresholdCount, carryThresholdCount, floorJump, Int.floor_div_natCast,
    Int.floor_natCast, Int.natCast_ediv]

theorem straightening_successor_inverse (p : ℕ) :
    (straighteningUnit p).val*((p+1 : ℕ) : ZMod (p^2))=1 := by
  have hp2 : (p : ZMod (p^2))^2=0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  change (1-(p : ZMod (p^2)))*((p+1 : ℕ) : ZMod (p^2))=1
  push_cast
  linear_combination -hp2

theorem literal_carry_dilated_field {p a : ℕ} (hp : p.Prime) (ha : a < p^2) :
    carryReading p a=
      weightedProfile (p-1) (fun _ => 1) ((((p+1)*a : ℕ) : ℝ)/((p^2 : ℕ) : ℝ)) := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let A := ((p+1)*a)%(p^2)
  have hA : A < p^2 := Nat.mod_lt _ (pow_pos hp.pos 2)
  have hcast : (A : ZMod (p^2))=((p+1 : ℕ) : ZMod (p^2))*(a : ZMod (p^2)) := by
    simp only [A, ZMod.natCast_mod, Nat.cast_mul]
  have he : straightenedAddress p A=a := by
    unfold straightenedAddress
    rw [hcast, ← mul_assoc, straightening_successor_inverse p, one_mul,
      ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have h := carry_representation (b := p) (A := A) hp.two_le hA
  rw [he] at h
  rw [unit_weights, periodic_grid_mod (boundaryResponse_periodic (p-1))
    (pow_pos hp.pos 2) ((p+1)*a)]
  simpa only [Nat.cast_pow] using h

theorem threshold_straightening {p a : ℕ} (hp : p.Prime) (ha : a < p^2) :
    (thresholdCount p a : ℝ)-(a : ℝ)/(p : ℝ)=
      weightedProfile (p-1) (fun _ => 1)
        (((p : ℝ)+1)*(a : ℝ)/(p : ℝ)^2) := by
  simpa only [literal_threshold_count, carryReading, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_pow] using literal_carry_dilated_field hp ha

theorem literal_class_centering {p q s : ℕ} (hp : p.Prime) (hs : s < p) :
    (fluctuationTable p (p*q+s) : ℝ)-(-((p-s : ℕ) : ℝ)/(p : ℝ))=
      carryReading p (p*q+s) := by
  rw [fluctuationTable_eq_thresholdCount hp.pos hs]
  unfold carryReading
  push_cast [Nat.cast_sub (Nat.le_of_lt hs)]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem class_centered_mean {p s : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hspos : 0 < s) (hs : s < p) :
    (1/(p : ℝ))*(∑ q ∈ Finset.range p, (fluctuationTable p (p*q+s) : ℝ))=
      -((p-s : ℕ) : ℝ)/(p : ℝ) := by
  have h := fluctuationTable_column_sum hp hodd hspos hs
  rw [← Int.cast_sum, h]
  push_cast [Nat.cast_sub (Nat.le_of_lt hs)]
  ring

theorem coherent_sampled_work (N Q : ℕ) :
    sampledWork N Q (fun _ => 1) (fun _ => 1)=sampledEnergy N Q := by
  simp only [sampledWork, sampledEnergy, unit_weights, ← pow_two]

theorem collision_energy_complete_readings {p : ℕ} (hp : p.Prime) :
    collisionEnergy hp=(p : ℝ)^2*sampledWork (p-1) (p^2) (fun _ => 1) (fun _ => 1) ∧
    collisionEnergy hp=(fun _ => (1 : ℝ)) ⬝ᵥ
      (sampledGram (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he := sampledEnergy_prime hp
  rw [← coherent_sampled_work] at he
  have hfirst : collisionEnergy hp=
      (p : ℝ)^2*sampledWork (p-1) (p^2) (fun _ => 1) (fun _ => 1) := by
    field_simp at he
    nlinarith
  refine ⟨hfirst,?_⟩
  rw [sampled_gram_mixed_normalized (p-1) (pow_pos hp.pos 2)]
  simp only [sampledWork, cutoff_complete_profile, Nat.cast_pow] at hfirst ⊢
  exact hfirst

end NField.ResetForests.GramDecomposition
