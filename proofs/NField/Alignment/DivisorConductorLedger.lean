/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExactConductorEnergy

/-! # The conductor ledger at every divisor of the ambient modulus -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorConductorLedger
open scoped BigOperators
open CollisionCharacterStructure ConductorBoundaryLedger ExactConductorEnergy

theorem pushdownUnit_val {d m : ℕ} [NeZero d] [NeZero m]
    (hd : d ∣ m) (u : UnitClass m) : (pushdownUnit hd u).val.val = u.val.val % d := by
  unfold pushdownUnit
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]

theorem pushdownUnit_eq_iff_val {d m : ℕ} [NeZero d] [NeZero m]
    (hd : d ∣ m) (u : UnitClass m) (r : UnitClass d) :
    pushdownUnit hd u = r ↔ u.val.val % d = r.val.val := by
  rw [← pushdownUnit_val hd u]
  constructor
  · intro h; rw [h]
  · intro h
    apply Units.ext
    exact ZMod.val_injective d h

theorem unitPushdown_self {m : ℕ} [NeZero m] (μ : UnitClass m → ℂ) :
    unitPushdown (dvd_refl m) μ = μ := by
  classical
  funext r
  simp only [unitPushdown, pushdownUnit, ZMod.unitsMap_self, MonoidHom.id_apply]
  apply Finset.sum_eq_single r
  · intro x hx hxr
    exact (hxr (Finset.mem_filter.mp hx).2).elim
  · intro hr
    exact (hr (by simp)).elim

theorem pushdownUnit_comp {m d e : ℕ} (hd : d ∣ m) (he : e ∣ d)
    (u : UnitClass m) :
    pushdownUnit he (pushdownUnit hd u) = pushdownUnit (he.trans hd) u := by
  exact DFunLike.congr_fun (ZMod.unitsMap_comp he hd) u

/-- Summing fibers in two stages equals summing the composite reduction fiber. -/
theorem unitPushdown_comp {m d e : ℕ} [NeZero m] [NeZero d] [NeZero e]
    (hd : d ∣ m) (he : e ∣ d) (μ : UnitClass m → ℂ) :
    unitPushdown he (unitPushdown hd μ) = unitPushdown (he.trans hd) μ := by
  classical
  funext r
  unfold unitPushdown
  calc
    (∑ y : UnitClass d with pushdownUnit he y = r,
        ∑ x : UnitClass m with pushdownUnit hd x = y, μ x) =
      ∑ y : UnitClass d, ∑ x : UnitClass m with pushdownUnit hd x = y,
        if pushdownUnit he y = r then μ x else 0 := by
          simp only [Finset.sum_filter, Finset.sum_ite_irrel, Finset.sum_const_zero]
    _ = ∑ y : UnitClass d, ∑ x : UnitClass m with pushdownUnit hd x = y,
        if pushdownUnit he (pushdownUnit hd x) = r then μ x else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x : UnitClass m,
        if pushdownUnit he (pushdownUnit hd x) = r then μ x else 0 :=
      Finset.sum_fiberwise Finset.univ (pushdownUnit hd)
        (fun x => if pushdownUnit he (pushdownUnit hd x) = r then μ x else 0)
    _ = _ := by simp only [pushdownUnit_comp, Finset.sum_filter]

theorem conductorLedgerTerm_pushdown {m d e : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (he : e ∣ d) (μ : UnitClass m → ℂ) :
    conductorLedgerTerm e (unitPushdown hd μ) = conductorLedgerTerm e μ := by
  letI : NeZero e := ⟨fun hz => NeZero.ne d (Nat.eq_zero_of_zero_dvd (hz ▸ he))⟩
  simp only [conductorLedgerTerm, he, he.trans hd, dite_true, unitPushdown_comp]

/-- The manuscript's formula for `P_D` in terms of the original ambient
pushdowns `M_e`, including every divisor `D`, not just the top conductor. -/
theorem exactConductorEnergy_cast_eq_ledger {m d : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (μ : UnitClass m → ℂ) :
    (exactConductorEnergy d μ : ℂ) =
      (1 / 2 : ℂ) * ∑ e ∈ d.divisors,
        (ArithmeticFunction.moebius (d / e) : ℂ) * conductorLedgerTerm e μ := by
  classical
  rw [exactConductorEnergy_eq_primitiveSourceEnergy hd (NeZero.pos d),
    primitiveSourceEnergy_cast_eq_primitiveOddBoundaryMoment,
    primitiveOddBoundaryMoment_conductorLedger]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [conductorLedgerTerm_pushdown hd (Nat.dvd_of_mem_divisors he)]

end NField.Alignment.DivisorConductorLedger
