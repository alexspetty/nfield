/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConstructiveClassPrimeMeans

/-! # Natural representatives of every coarse unit fiber -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.UnitFiberMeans

open scoped BigOperators
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionPrimeLimits

def unitFiberCoordinate {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) (k : Fin (b ^ ell)) : UnitClass (allLagModulus b ell) :=
  ZMod.unitOfCoprime (u.val.val + b * k.val) (by
    have hu : u.val.val.Coprime b := by
      apply (ZMod.isUnit_iff_coprime u.val.val b).mp
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    exact ((Nat.coprime_add_mul_left_left u.val.val b k.val).2 hu).pow_right (ell + 1))

theorem unitFiberCoordinate_val {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) (k : Fin (b ^ ell)) :
    (unitFiberCoordinate u k).val.val = u.val.val + b * k.val := by
  have hlt : u.val.val + b * k.val < allLagModulus b ell := by
    have hu := u.val.val_lt
    have hk := k.isLt
    unfold allLagModulus
    rw [pow_succ]
    nlinarith
  unfold unitFiberCoordinate
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

theorem coarseUnitReduction_unitFiberCoordinate {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (u : UnitClass b) (k : Fin (b ^ ell)) :
    coarseUnitReduction b ell (unitFiberCoordinate u k) = u := by
  apply Units.ext
  unfold coarseUnitReduction unitFiberCoordinate
  rw [ZMod.unitsMap_val]
  simp only [ZMod.coe_unitOfCoprime]
  rw [ZMod.cast_natCast (show b ∣ allLagModulus b ell by
    unfold allLagModulus
    exact dvd_pow_self b (by omega))]
  rw [Nat.cast_add, Nat.cast_mul]
  simp

def unitFiberEquiv {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) : Fin (b ^ ell) ≃ Fiber (coarseUnitReduction b ell) u := by
  let toFiber : Fin (b ^ ell) → Fiber (coarseUnitReduction b ell) u :=
    fun k => ⟨unitFiberCoordinate u k, coarseUnitReduction_unitFiberCoordinate u k⟩
  apply Equiv.ofBijective toFiber
  constructor
  · intro k j h
    apply Fin.ext
    have hv := congrArg (fun a : Fiber (coarseUnitReduction b ell) u => a.val.val.val) h
    change (unitFiberCoordinate u k).val.val = (unitFiberCoordinate u j).val.val at hv
    rw [unitFiberCoordinate_val, unitFiberCoordinate_val] at hv
    exact Nat.mul_left_cancel (NeZero.pos b) (Nat.add_left_cancel hv)
  · intro a
    have hmod : a.val.val.val % b = u.val.val := by
      have hv := congrArg (fun v : UnitClass b => v.val.val) a.property
      unfold coarseUnitReduction at hv
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast] at hv
      exact hv
    have hk : a.val.val.val / b < b ^ ell := by
      apply (Nat.div_lt_iff_lt_mul (NeZero.pos b)).2
      simpa [allLagModulus, pow_succ] using a.val.val.val_lt
    let k : Fin (b ^ ell) := ⟨a.val.val.val / b, hk⟩
    refine ⟨k, Subtype.ext ?_⟩
    change unitFiberCoordinate u k = a.val
    apply Units.ext
    apply ZMod.val_injective
    rw [unitFiberCoordinate_val]
    dsimp [k]
    simpa [Nat.add_comm] using (hmod ▸ Nat.mod_add_div a.val.val.val b)

/-- Title: `The intrinsic unit fiber mean equals its exact natural table mean`. -/
theorem real_fiber_mean_eq_table {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (realUnitCollisionTable b ell) u =
      (b ^ ell : ℝ)⁻¹ * (tableFiberSum b ell u.val.val : ℝ) := by
  classical
  have hu : u.val.val ∈ reducedResidues b := by
    have hcop : u.val.val.Coprime b := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    have hpos : 1 ≤ u.val.val := by
      by_contra h
      have hz : u.val.val = 0 := by omega
      rw [hz] at hcop
      simp only [Nat.coprime_zero_left] at hcop
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, u.val.val_lt⟩, hcop⟩
  have hcard : Fintype.card (Fiber (coarseUnitReduction b ell) u) = b ^ ell := by
    simpa using Fintype.card_congr (unitFiberEquiv (ell := ell) u).symm
  have hsum : (∑ a : Fiber (coarseUnitReduction b ell) u,
      realUnitCollisionTable b ell a.val) = (tableFiberSum b ell u.val.val : ℝ) := by
    calc
      _ = ∑ k : Fin (b ^ ell), (allLagTable b ell (u.val.val + b * k.val) : ℝ) := by
        symm
        apply Fintype.sum_equiv (unitFiberEquiv u)
        intro k
        change _ = (allLagTable b ell (unitFiberCoordinate u k).val.val : ℝ)
        rw [unitFiberCoordinate_val]
      _ = ∑ k ∈ Finset.range (b ^ ell), (allLagTable b ell (u.val.val + b * k) : ℝ) :=
        Fin.sum_univ_eq_sum_range
          (fun k : ℕ => (allLagTable b ell (u.val.val + b * k) : ℝ)) (b ^ ell)
      _ = (tableFiberSum b ell u.val.val : ℝ) := by
        rw [tableFiberSum, tableFiber_eq_coordinates hb hu, fiberCoordinates,
          Finset.sum_image]
        · push_cast
          rfl
        · intro k _ j _ h
          exact Nat.mul_left_cancel (NeZero.pos b) (Nat.add_left_cancel h)
  simp only [fiberMean, hcard, hsum, Nat.cast_pow]

end NField.Alignment.UnitFiberMeans
