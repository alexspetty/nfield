/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenConductorSpectrum
import NField.Alignment.IntegerConductorLedger

/-! # The base-fifteen ledger measures the actual digit-boundary energy -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BaseFifteenActualEnergy
open scoped BigOperators
open CarryBoundarySpectra BaseFifteenConductorSpectrum IntegerConductorLedger
open ExactConductorEnergy

def digitWeightZ (x : ZMod 225) : ℤ := if x.val / 15 = x.val % 15 then 1 else 0

def digitWeight (x : ZMod 225) : ℂ := digitWeightZ x

def boundary : CollisionCharacterStructure.UnitClass 225 → ℂ :=
  integerBoundary 225 baseFifteenBoundaryWeight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem endpoint_boundary_is_digit_boundary : ∀ x : ZMod 225,
    baseFifteenBoundaryWeight x.val = digitWeightZ (x - 1) - digitWeightZ x := by
  decide

theorem boundary_is_actual : unitBoundarySignal digitWeight = boundary := by
  funext u
  simp only [unitBoundarySignal, signedBoundary, digitWeight, boundary, integerBoundary,
    endpoint_boundary_is_digit_boundary, Int.cast_sub]

theorem integer_difference_eq (d : ℕ) :
    integerDifference 225 d baseFifteenBoundaryWeight = baseFifteenLedgerDifference d := rfl

theorem ledger_difference_even {d : ℕ} (hd : d ∣ 225) :
    (2 : ℤ) ∣ baseFifteenLedgerDifference d := by
  rcases base_fifteen_complete_pushdown_ledger with
    ⟨h1, h3, h5, h9, h15, h25, h45, h75, h225⟩
  have hdiv : Nat.divisors 225 = ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ) := by decide
  have hmem : d ∈ Nat.divisors 225 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [h1, h3, h5, h9, h15, h25, h45, h75, h225]

theorem actual_energy_eq_integer_ledger {d : ℕ} [NeZero d] (hd : d ∣ 225) :
    exactConductorEnergy d boundary = (baseFifteenExactConductorEnergyLedger d : ℝ) := by
  apply exactConductorEnergy_eq_of_integer_ledger hd baseFifteenBoundaryWeight
  simp only [integer_difference_eq, baseFifteenExactConductorEnergyLedger]
  have heven : (2 : ℤ) ∣ ∑ e ∈ d.divisors,
      ArithmeticFunction.moebius (d / e) * (e.totient : ℤ) * baseFifteenLedgerDifference e := by
    apply Finset.dvd_sum
    intro e he
    exact dvd_mul_of_dvd_right
      (ledger_difference_even ((Nat.dvd_of_mem_divisors he).trans hd)) _
  exact (Int.ediv_mul_cancel heven).symm.trans (mul_comm _ _)

theorem actual_conductor_spectrum :
    exactConductorEnergy 1 boundary = 0 ∧
    exactConductorEnergy 3 boundary = 0 ∧
    exactConductorEnergy 5 boundary = 0 ∧
    exactConductorEnergy 9 boundary = 24 ∧
    exactConductorEnergy 15 boundary = 0 ∧
    exactConductorEnergy 25 boundary = 240 ∧
    exactConductorEnergy 45 boundary = 360 ∧
    exactConductorEnergy 75 boundary = 400 ∧
    exactConductorEnergy 225 boundary = 896 := by
  rcases base_fifteen_exact_conductor_spectrum with
    ⟨h1, h3, h5, h9, h15, h25, h45, h75, h225⟩
  have he (d : ℕ) [NeZero d] (hd : d ∣ 225) := actual_energy_eq_integer_ledger hd
  norm_num [he 1 (by decide), he 3 (by decide), he 5 (by decide), he 9 (by decide),
    he 15 (by decide), he 25 (by decide), he 45 (by decide), he 75 (by decide),
    he 225 (by decide), h1, h3, h5, h9, h15, h25, h45, h75, h225]

theorem actual_full_odd_energy : fullOddBoundaryEnergy boundary = 1920 := by
  rcases actual_conductor_spectrum with ⟨h1, h3, h5, h9, h15, h25, h45, h75, h225⟩
  have hdiv : Nat.divisors 225 = ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ) := by decide
  rw [fullOddBoundaryEnergy_eq_sum_exactConductor]
  norm_num [hdiv, h1, h3, h5, h9, h15, h25, h45, h75, h225]

theorem actual_proper_energy : properConductorEnergy boundary = 1024 := by
  have h := fullOddBoundaryEnergy_eq_top_add_proper boundary
  rw [actual_full_odd_energy, actual_conductor_spectrum.2.2.2.2.2.2.2.2] at h
  linarith

theorem actual_digit_energy_split :
    properConductorEnergy (unitBoundarySignal digitWeight) = 1024 ∧
    exactConductorEnergy 225 (unitBoundarySignal digitWeight) = 896 ∧
    fullOddBoundaryEnergy (unitBoundarySignal digitWeight) = 1920 := by
  rw [boundary_is_actual]
  exact ⟨actual_proper_energy, actual_conductor_spectrum.2.2.2.2.2.2.2.2,
    actual_full_odd_energy⟩

end NField.Alignment.BaseFifteenActualEnergy
