/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DivisorConductorLedger

/-! # Integer residue ledgers certify the actual character energies -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerConductorLedger
open scoped BigOperators
open CollisionCharacterStructure ConductorBoundaryLedger ExactConductorEnergy
open DivisorConductorLedger

noncomputable def unitResidueEquiv (m : ℕ) [NeZero m] :
    UnitClass m ≃ {r : ℕ // r ∈ (Finset.range m).filter (fun r => r.Coprime m)} where
  toFun u := ⟨u.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr u.val.val_lt, ZMod.val_coe_unit_coprime u⟩⟩
  invFun r := ZMod.unitOfCoprime r.val (Finset.mem_filter.mp r.property).2
  left_inv u := by
    apply Units.ext
    exact ZMod.natCast_zmod_val u.val
  right_inv r := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1)

theorem sum_units_val {A : Type*} [AddCommMonoid A]
    (m : ℕ) [NeZero m] (f : ℕ → A) :
    (∑ u : UnitClass m, f u.val.val) =
      ∑ r ∈ Finset.range m, if r.Coprime m then f r else 0 := by
  classical
  calc
    _ = ∑ r : {r : ℕ // r ∈ (Finset.range m).filter (fun r => r.Coprime m)}, f r := by
      exact Fintype.sum_equiv (unitResidueEquiv m) _ _ (fun _ => rfl)
    _ = ∑ r ∈ (Finset.range m).filter (fun r => r.Coprime m), f r :=
      (Finset.sum_subtype _ (by intro r; rfl) f).symm
    _ = _ := Finset.sum_filter _ _

def integerPushdown (m d : ℕ) (w : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ x ∈ Finset.range m, if x.Coprime m ∧ x % d = r % d then w x else 0

def integerDifference (m d : ℕ) (w : ℕ → ℤ) : ℤ :=
  (∑ r ∈ Finset.range d, if r.Coprime d then integerPushdown m d w r ^ 2 else 0) -
    ∑ r ∈ Finset.range d, if r.Coprime d then
      integerPushdown m d w r * integerPushdown m d w ((d - r) % d) else 0

def integerBoundary (m : ℕ) (w : ℕ → ℤ) (u : UnitClass m) : ℂ := w u.val.val

theorem unitPushdown_eq_integer {m d : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (w : ℕ → ℤ) (r : UnitClass d) :
    unitPushdown hd (integerBoundary m w) r = integerPushdown m d w r.val.val := by
  classical
  simp only [unitPushdown, Finset.sum_filter, pushdownUnit_eq_iff_val, integerBoundary]
  rw [sum_units_val m (fun x => if x % d = r.val.val then (w x : ℂ) else 0)]
  simp [integerPushdown, Nat.mod_eq_of_lt r.val.val_lt, ite_and]

theorem conductorLedgerTerm_eq_integer {m d : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (w : ℕ → ℤ) :
    conductorLedgerTerm d (integerBoundary m w) =
      (d.totient : ℂ) * (integerDifference m d w : ℂ) := by
  classical
  simp only [conductorLedgerTerm, hd, dite_true, unitPushdown_eq_integer,
    star_intCast, Units.val_neg, ZMod.neg_val']
  rw [sum_units_val d (fun r => (integerPushdown m d w r : ℂ) * integerPushdown m d w r),
    sum_units_val d (fun r => (integerPushdown m d w r : ℂ) *
      integerPushdown m d w ((d - r) % d))]
  simp [integerDifference, pow_two]

/-- An exact integer identity for twice the energy certifies the real
character energy; no rounded arithmetic or integer division is assumed. -/
theorem exactConductorEnergy_eq_of_integer_ledger
    {m d : ℕ} [NeZero m] [NeZero d] (hd : d ∣ m) (w : ℕ → ℤ) (z : ℤ)
    (hz : (∑ e ∈ d.divisors,
      ArithmeticFunction.moebius (d / e) * (e.totient : ℤ) * integerDifference m e w) = 2 * z) :
    exactConductorEnergy d (integerBoundary m w) = (z : ℝ) := by
  classical
  apply Complex.ofReal_injective
  rw [exactConductorEnergy_cast_eq_ledger hd]
  have hsum :
      (∑ e ∈ d.divisors, (ArithmeticFunction.moebius (d / e) : ℂ) *
        conductorLedgerTerm e (integerBoundary m w)) =
      ((∑ e ∈ d.divisors, ArithmeticFunction.moebius (d / e) *
        (e.totient : ℤ) * integerDifference m e w : ℤ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro e he
    letI : NeZero e := ⟨(Nat.pos_of_mem_divisors he).ne'⟩
    rw [conductorLedgerTerm_eq_integer ((Nat.dvd_of_mem_divisors he).trans hd)]
    ring
  rw [hsum, hz]
  push_cast
  ring

end NField.Alignment.IntegerConductorLedger
