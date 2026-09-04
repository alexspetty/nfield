/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryEnergyBridge
import NField.Alignment.AnalyticCollisionTransform

/-!
# Prime carry fiber centering

The coarse fibers modulo a prime are parametrized explicitly by one complete
column of the prime-square carry table.  This identifies the intrinsic fiber
centering used by the collision transform with the closed class means proved
from the concrete floor-jump table.
-/

namespace NField.Alignment.PrimeCarryFiberCentering

open scoped BigOperators ZMod
open NField.Alignment.AnalyticCollisionTransform
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.TheCollisionSpectrum

/-- The unit in one prime-square coarse fiber with column coordinate `q`. -/
noncomputable def primeFiberCoordinate
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (_hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    UnitClass (allLagModulus p 1) :=
  ZMod.unitOfCoprime (u.val.val + p * q.val) (by
    have hu : u.val.val.Coprime p := by
      apply (ZMod.isUnit_iff_coprime u.val.val p).mp
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    simpa [allLagModulus] using
      ((Nat.coprime_add_mul_left_left u.val.val p q.val).2 hu).pow_right 2)

theorem primeFiberCoordinate_val
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    (primeFiberCoordinate hp u q).val.val = u.val.val + p * q.val := by
  unfold primeFiberCoordinate
  have hlt : u.val.val + p * q.val < p ^ 2 := by
    have hu := u.val.val_lt
    have hq := q.isLt
    nlinarith
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  simpa [allLagModulus] using Nat.mod_eq_of_lt hlt

theorem coarseUnitReduction_primeFiberCoordinate
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    coarseUnitReduction p 1 (primeFiberCoordinate hp u q) = u := by
  apply Units.ext
  unfold coarseUnitReduction primeFiberCoordinate
  rw [ZMod.unitsMap_val]
  simp only [ZMod.coe_unitOfCoprime]
  rw [ZMod.cast_natCast (show p ∣ allLagModulus p 1 by
    unfold allLagModulus
    exact dvd_pow_self p (by omega))]
  rw [Nat.cast_add, Nat.cast_mul]
  simp

/-- Every coarse prime-square fiber is exactly one `p`-entry carry column. -/
noncomputable def primeFiberEquiv
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (u : UnitClass p) :
    Fin p ≃ Fiber (coarseUnitReduction p 1) u := by
  let toFiber : Fin p → Fiber (coarseUnitReduction p 1) u :=
    fun q => ⟨primeFiberCoordinate hp u q,
      coarseUnitReduction_primeFiberCoordinate hp u q⟩
  apply Equiv.ofBijective toFiber
  constructor
  · intro q r hqr
    apply Fin.ext
    have hv := congrArg
      (fun a : Fiber (coarseUnitReduction p 1) u => a.val.val.val) hqr
    change (primeFiberCoordinate hp u q).val.val =
      (primeFiberCoordinate hp u r).val.val at hv
    rw [primeFiberCoordinate_val, primeFiberCoordinate_val] at hv
    have hmul : p * q.val = p * r.val := Nat.add_left_cancel hv
    exact Nat.mul_left_cancel hp.pos hmul
  · intro a
    have hmod : a.val.val.val % p = u.val.val := by
      have hv := congrArg
        (fun v : UnitClass p => v.val.val) a.property
      unfold coarseUnitReduction at hv
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast] at hv
      exact hv
    have hqLt : a.val.val.val / p < p := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      have ha := a.val.val.val_lt
      simpa [allLagModulus, pow_two] using ha
    let q : Fin p := ⟨a.val.val.val / p, hqLt⟩
    refine ⟨q, Subtype.ext ?_⟩
    change primeFiberCoordinate hp u q = a.val
    apply Units.ext
    apply ZMod.val_injective
    rw [primeFiberCoordinate_val]
    dsimp [q]
    simpa [Nat.add_comm] using (hmod ▸ Nat.mod_add_div a.val.val.val p)

/-- The general lag-one table specializes definitionally to the concrete
prime carry table. -/
theorem allLagUnitTable_one_eq_fluctuationTable
    {p : ℕ} [NeZero (allLagModulus p 1)]
    (_hp : p.Prime) (a : UnitClass (allLagModulus p 1)) :
    allLagUnitTable p 1 a = (fluctuationTable p a.val.val : ℂ) := by
  unfold allLagUnitTable allLagTable fluctuationTable
  simp only [allLagModulus, Nat.reduceAdd, pow_two]
  rw [allLagDiagonal_one_eq_diagonalSlices]

/-- The intrinsic mean on a coarse unit fiber is the exact rational column
mean of the floor-jump table. -/
theorem primeCarry_fiberMean
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2) (u : UnitClass p) :
    fiberMean (coarseUnitReduction p 1) (allLagUnitTable p 1) u =
      -((p - u.val.val : ℕ) : ℂ) / (p : ℂ) := by
  classical
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hspos : 0 < u.val.val :=
    ZMod.val_pos.mpr (IsUnit.ne_zero u.isUnit)
  have hslt : u.val.val < p := u.val.val_lt
  have hsum := fluctuationTable_column_sum hp hpodd hspos hslt
  have hcard : Fintype.card (Fiber (coarseUnitReduction p 1) u) = p :=
    by simpa using Fintype.card_congr (primeFiberEquiv hp u).symm
  unfold fiberMean
  rw [hcard]
  have hreindex :
      (∑ a : Fiber (coarseUnitReduction p 1) u,
          allLagUnitTable p 1 a.val) =
        ∑ q : Fin p,
          (fluctuationTable p (p * q.val + u.val.val) : ℂ) := by
    symm
    apply Fintype.sum_equiv (primeFiberEquiv hp u)
    intro q
    change (fluctuationTable p (p * q.val + u.val.val) : ℂ) =
      allLagUnitTable p 1 (primeFiberCoordinate hp u q)
    rw [allLagUnitTable_one_eq_fluctuationTable hp]
    rw [primeFiberCoordinate_val]
    congr 2
    omega
  rw [hreindex]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (fluctuationTable p (p * q + u.val.val) : ℂ)) p]
  rw [← Int.cast_sum, hsum]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_sub (Nat.le_of_lt hslt)]
  push_cast
  field_simp [hpC]
  ring

/-- The class-centered concrete carry table is exactly the natural centered
lag-one collision transform. -/
theorem centeredLagOneSpectrum_eq_primeCarryCentered
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2)
    (a : UnitClass (p ^ 2)) :
    centeredLagOneSpectrum p a = primeCarryCentered hp a := by
  have hredval : (coarseUnitReduction p 1 a).val.val = a.val.val % p := by
    unfold coarseUnitReduction
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
    rfl
  unfold centeredLagOneSpectrum centeredCollisionTransform centeredSignal
  rw [allLagUnitTable_one_eq_fluctuationTable hp,
    primeCarry_fiberMean hp hpodd, hredval]
  unfold primeCarryCentered
  rw [neg_div, sub_neg_eq_add]
  rfl

end NField.Alignment.PrimeCarryFiberCentering
