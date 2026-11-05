/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PushdownParity
import NField.Alignment.DivisorConductorLedger
import NField.Alignment.CarryBoundarySpectra

/-! # The increasing two-digit base-five boundary, as an exact finite witness -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IncreasingDigitBoundary
open scoped BigOperators
open CollisionCharacterStructure CarryBoundarySpectra ConductorBoundaryLedger
open ExactConductorEnergy PrimitiveOddBoundaryMean PushdownParity
open DivisorConductorLedger

def cellWeightZ (x : ZMod 25) : ℤ := if x.val / 5 < x.val % 5 then 1 else 0

def boundaryZ (u : UnitClass 25) : ℤ := cellWeightZ (u.val - 1) - cellWeightZ u.val

def cellWeight (x : ZMod 25) : ℂ := cellWeightZ x

def boundary (u : UnitClass 25) : ℂ := boundaryZ u

theorem selected_cells : ∀ x : ZMod 25,
    (x.val / 5 < x.val % 5) ↔ x.val ∈ ({1, 2, 3, 4, 7, 8, 9, 13, 14, 19} : Finset ℕ) := by
  decide

theorem boundary_support : ∀ u : UnitClass 25,
    boundaryZ u = if u.val.val ∈ ({1, 7, 13, 19} : Finset ℕ) then -1 else 0 := by
  decide

theorem boundary_is_actual : unitBoundarySignal cellWeight = boundary := by
  funext u
  simp only [unitBoundarySignal, signedBoundary, cellWeight, boundary, boundaryZ, Int.cast_sub]

theorem integer_pushdown_five : ∀ r : UnitClass 5,
    (∑ u : UnitClass 25, if u.val.val % 5 = r.val.val then boundaryZ u else 0) = -1 := by
  decide

theorem integer_square_sum : (∑ u : UnitClass 25, boundaryZ u ^ 2) = 4 := by decide

theorem integer_antipodal_sum :
    (∑ u : UnitClass 25, boundaryZ u * boundaryZ (-u)) = 0 := by decide

theorem pushdown_five (r : UnitClass 5) :
    unitPushdown (by norm_num : 5 ∣ 25) boundary r = -1 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (integer_pushdown_five r)
  push_cast at h
  simpa only [unitPushdown, Finset.sum_filter, pushdownUnit_eq_iff_val, boundary] using h

theorem lower_energy_zero : exactConductorEnergy 5 boundary = 0 :=
  exactConductorEnergy_zero_of_even_pushdown (by norm_num : 5 ∣ 25) boundary
    (fun r => (pushdown_five (-r)).trans (pushdown_five r).symm)

theorem lower_pushdown_nonzero :
    unitPushdown (by norm_num : 5 ∣ 25) boundary (1 : UnitClass 5) ≠ 0 := by
  rw [pushdown_five]
  norm_num

theorem square_sum : (∑ u : UnitClass 25, boundary u * star (boundary u)) = 4 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) integer_square_sum
  push_cast at h
  simpa [boundary, pow_two] using h

theorem antipodal_sum :
    (∑ u : UnitClass 25, boundary u * star (boundary (-u))) = 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) integer_antipodal_sum
  push_cast at h
  simpa [boundary] using h

theorem ledger_five : conductorLedgerTerm 5 boundary = 0 := by
  simp [conductorLedgerTerm, pushdown_five]

theorem ledger_twentyfive : conductorLedgerTerm 25 boundary = 80 := by
  have hφ : Nat.totient 25 = 20 := by decide
  simp only [conductorLedgerTerm, dvd_refl, dite_true, unitPushdown_self, hφ]
  change (20 : ℂ) * ((∑ u : UnitClass 25, boundary u * star (boundary u)) -
    (∑ u : UnitClass 25, boundary u * star (boundary (-u)))) = 80
  rw [square_sum, antipodal_sum]
  norm_num

theorem primitive_moment : primitiveOddBoundaryMoment boundary = 40 := by
  have hd : Nat.divisors 25 = ({1, 5, 25} : Finset ℕ) := by decide
  have hμ : ArithmeticFunction.moebius 25 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow
      (p := 5) (k := 2) (by norm_num) (by norm_num)
  rw [primitiveOddBoundaryMoment_conductorLedger]
  norm_num [hd, hμ, ledger_five, ledger_twentyfive]

theorem top_energy : exactConductorEnergy 25 boundary = 40 := by
  apply Complex.ofReal_injective
  rw [exactConductorEnergy_eq_primitiveSourceEnergy (dvd_refl 25) (by norm_num),
    primitiveSourceEnergy_cast_eq_primitiveOddBoundaryMoment,
    unitPushdown_self, primitive_moment]
  norm_num

/-- The literal digit predicate has nonzero even pushdown, zero lower energy,
and positive top-conductor energy, exactly as printed in the manuscript. -/
theorem actual_digit_boundary_witness :
    (∀ r : UnitClass 5,
      unitPushdown (by norm_num : 5 ∣ 25) (unitBoundarySignal cellWeight) r = -1) ∧
    exactConductorEnergy 5 (unitBoundarySignal cellWeight) = 0 ∧
    exactConductorEnergy 25 (unitBoundarySignal cellWeight) = 40 := by
  rw [boundary_is_actual]
  exact ⟨pushdown_five, lower_energy_zero, top_energy⟩

theorem energy_one_zero : exactConductorEnergy 1 boundary = 0 := by
  apply exactConductorEnergy_zero_of_even_pushdown (one_dvd 25) boundary
  intro r
  exact congrArg (unitPushdown (one_dvd 25) boundary) (Subsingleton.elim (-r) r)

theorem full_energy : fullOddBoundaryEnergy boundary = 40 := by
  have hd : Nat.divisors 25 = ({1, 5, 25} : Finset ℕ) := by decide
  rw [fullOddBoundaryEnergy_eq_sum_exactConductor]
  norm_num [hd, energy_one_zero, lower_energy_zero, top_energy]

theorem proper_energy_zero : properConductorEnergy boundary = 0 := by
  have h := fullOddBoundaryEnergy_eq_top_add_proper boundary
  rw [full_energy, top_energy] at h
  linarith

theorem actual_top_concentration :
    properConductorEnergy (unitBoundarySignal cellWeight) = 0 ∧
    fullOddBoundaryEnergy (unitBoundarySignal cellWeight) = 40 := by
  rw [boundary_is_actual]
  exact ⟨proper_energy_zero, full_energy⟩

end NField.Alignment.IncreasingDigitBoundary
