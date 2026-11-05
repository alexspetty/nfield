/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacteristicCycles

/-!
# Haar pairing of arbitrary finite residue tables

The generalized CRT gives one point in the common period for each pair
of compatible residues. The resulting formula is an actual Haar integral,
with both real and imaginary parts retained and no coprimality restriction.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResiduePairing

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionCharacteristicCycles
open CollisionDivisibilityCovariance

theorem residue_pair_count_complex {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (a b : ℕ) :
    (∑ n ∈ Finset.range (d.lcm e),
      if Nat.ModEq d n a ∧ Nat.ModEq e n b then (1 : ℂ) else 0) =
      if Nat.ModEq (d.gcd e) a b then 1 else 0 := by
  exact_mod_cast residue_pair_count hd he a b

theorem residue_table_pair {d e : ℕ} [NeZero d] [NeZero e]
    (F : ZMod d → ℂ) (G : ZMod e → ℂ) :
    (∫ x, F (residueHom d x).toAdd * G (residueHom e x).toAdd ∂phaseHaar) =
      (1 / (d.lcm e : ℂ)) * ∑ a : ZMod d, ∑ b : ZMod e,
        if Nat.ModEq (d.gcd e) a.val b.val then F a * G b else 0 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  letI : NeZero (d.lcm e) := ⟨(Nat.lcm_pos hd he).ne'⟩
  have hpoint (n : ℕ) : F (n : ZMod d) * G (n : ZMod e) =
      ∑ a : ZMod d, ∑ b : ZMod e,
        if Nat.ModEq d n a.val ∧ Nat.ModEq e n b.val then F a * G b else 0 := by
    simp_rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ite_and]
    simp
  have hgrid (x : Phase) :
      F (residueHom d x).toAdd * G (residueHom e x).toAdd =
        F ((residueHom (d.lcm e) x).toAdd.val : ZMod d) *
          G ((residueHom (d.lcm e) x).toAdd.val : ZMod e) := by
    rw [residue_compatible (Nat.dvd_lcm_left d e),
      residue_compatible (Nat.dvd_lcm_right d e)]
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
  simp_rw [hgrid]
  rw [integral_residue_complex (d.lcm e)
    (fun n => F (n : ZMod d) * G (n : ZMod e))]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  have hsum (a : ZMod d) :
      (∑ n ∈ Finset.range (d.lcm e), ∑ b : ZMod e,
        if Nat.ModEq d n a.val ∧ Nat.ModEq e n b.val then F a * G b else 0) =
      ∑ b : ZMod e,
        if Nat.ModEq (d.gcd e) a.val b.val then F a * G b else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    calc
      _ = (F a * G b) * ∑ n ∈ Finset.range (d.lcm e),
          if Nat.ModEq d n a.val ∧ Nat.ModEq e n b.val then (1 : ℂ) else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      _ = _ := by
        rw [residue_pair_count_complex hd he]
        split_ifs <;> simp
  simp_rw [hsum]
  ring

theorem compatible_table_sum {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (π : α → γ) (σ : β → γ) (F : α → ℂ) (G : β → ℂ) :
    (∑ a, ∑ b, if π a = σ b then F a * G b else 0) =
      ∑ t, (∑ a, if π a = t then F a else 0) *
        (∑ b, if σ b = t then G b else 0) := by
  symm
  have hexpand (t : γ) :
      (∑ a, if π a = t then F a else 0) * (∑ b, if σ b = t then G b else 0) =
      ∑ a, ∑ b, (if π a = t then F a else 0) * (if σ b = t then G b else 0) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (π a)]
  · simp [eq_comm]
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

theorem residue_table_pair_fibers {d e : ℕ} [NeZero d] [NeZero e]
    [NeZero (d.gcd e)] (F : ZMod d → ℂ) (G : ZMod e → ℂ) :
    (∫ x, F (residueHom d x).toAdd * G (residueHom e x).toAdd ∂phaseHaar) =
      (1 / (d.lcm e : ℂ)) * ∑ t : ZMod (d.gcd e),
        (∑ a : ZMod d,
          if ZMod.castHom (Nat.gcd_dvd_left d e) (ZMod (d.gcd e)) a = t
          then F a else 0) *
        (∑ b : ZMod e,
          if ZMod.castHom (Nat.gcd_dvd_right d e) (ZMod (d.gcd e)) b = t
          then G b else 0) := by
  rw [residue_table_pair]
  congr 1
  have hcondition (a : ZMod d) (b : ZMod e) :
      Nat.ModEq (d.gcd e) a.val b.val ↔
        ZMod.castHom (Nat.gcd_dvd_left d e) (ZMod (d.gcd e)) a =
          ZMod.castHom (Nat.gcd_dvd_right d e) (ZMod (d.gcd e)) b := by
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]
  simp_rw [hcondition]
  simpa only using compatible_table_sum
    (ZMod.castHom (Nat.gcd_dvd_left d e) (ZMod (d.gcd e)))
    (ZMod.castHom (Nat.gcd_dvd_right d e) (ZMod (d.gcd e))) F G

end NField.Alignment.CollisionResiduePairing
