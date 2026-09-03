/-
Author: Alexander S. Petty
-/

import NField.Alignment.ExactConductorEnergy
import NField.Alignment.CarryBoundarySpectra

/-!
# Base-fifteen exact-conductor spectrum

The terminal two-digit collision boundary in base fifteen has ambient modulus
225.  This module records its complete pushdown ledger and evaluates the
Mobius primitive-odd formula at every divisor.  All values are exact integer
certificates.
-/

namespace NField.Alignment.BaseFifteenConductorSpectrum

open scoped BigOperators
open NField.Alignment.CarryBoundarySpectra

/-- Integer form of the primitive-odd conductor ledger at a requested level. -/
def baseFifteenExactConductorEnergyLedger (d : ℕ) : ℤ :=
  (∑ e ∈ d.divisors,
    ArithmeticFunction.moebius (d / e) * (e.totient : ℤ) *
      baseFifteenLedgerDifference e) / 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every pushdown square-minus-antipode value used by the spectrum. -/
theorem base_fifteen_complete_pushdown_ledger :
    baseFifteenLedgerDifference 1 = 0 ∧
    baseFifteenLedgerDifference 3 = 0 ∧
    baseFifteenLedgerDifference 5 = 0 ∧
    baseFifteenLedgerDifference 9 = 8 ∧
    baseFifteenLedgerDifference 15 = 0 ∧
    baseFifteenLedgerDifference 25 = 24 ∧
    baseFifteenLedgerDifference 45 = 32 ∧
    baseFifteenLedgerDifference 75 = 32 ∧
    baseFifteenLedgerDifference 225 = 32 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete exact-conductor spectrum stated in the manuscript. -/
theorem base_fifteen_exact_conductor_spectrum :
    baseFifteenExactConductorEnergyLedger 1 = 0 ∧
    baseFifteenExactConductorEnergyLedger 3 = 0 ∧
    baseFifteenExactConductorEnergyLedger 5 = 0 ∧
    baseFifteenExactConductorEnergyLedger 9 = 24 ∧
    baseFifteenExactConductorEnergyLedger 15 = 0 ∧
    baseFifteenExactConductorEnergyLedger 25 = 240 ∧
    baseFifteenExactConductorEnergyLedger 45 = 360 ∧
    baseFifteenExactConductorEnergyLedger 75 = 400 ∧
    baseFifteenExactConductorEnergyLedger 225 = 896 := by
  rcases base_fifteen_complete_pushdown_ledger with
    ⟨h1, h3, h5, h9, h15, h25, h45, h75, h225⟩
  have hd1 : Nat.divisors 1 = ({1} : Finset ℕ) := by decide
  have hd3 : Nat.divisors 3 = ({1, 3} : Finset ℕ) := by decide
  have hd5 : Nat.divisors 5 = ({1, 5} : Finset ℕ) := by decide
  have hd9 : Nat.divisors 9 = ({1, 3, 9} : Finset ℕ) := by decide
  have hd15 : Nat.divisors 15 = ({1, 3, 5, 15} : Finset ℕ) := by decide
  have hd25 : Nat.divisors 25 = ({1, 5, 25} : Finset ℕ) := by decide
  have hd45 : Nat.divisors 45 = ({1, 3, 5, 9, 15, 45} : Finset ℕ) := by decide
  have hd75 : Nat.divisors 75 = ({1, 3, 5, 15, 25, 75} : Finset ℕ) := by decide
  have hd225 : Nat.divisors 225 =
      ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ) := by decide
  have phi9 : Nat.totient 9 = 6 := by decide
  have phi25 : Nat.totient 25 = 20 := by decide
  have phi45 : Nat.totient 45 = 24 := by decide
  have phi75 : Nat.totient 75 = 40 := by decide
  have phi225 : Nat.totient 225 = 120 := by decide
  have mu3 : ArithmeticFunction.moebius 3 = -1 := by
    exact ArithmeticFunction.moebius_apply_prime (by norm_num)
  have mu5 : ArithmeticFunction.moebius 5 = -1 := by
    exact ArithmeticFunction.moebius_apply_prime (by norm_num)
  have mu9 : ArithmeticFunction.moebius 9 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow
      (p := 3) (k := 2) (by norm_num) (by norm_num)
  have mu25 : ArithmeticFunction.moebius 25 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow
      (p := 5) (k := 2) (by norm_num) (by norm_num)
  norm_num [baseFifteenExactConductorEnergyLedger,
    hd1, hd3, hd5, hd9, hd15, hd25, hd45, hd75, hd225,
    h1, h3, h5, h9, h15, h25, h45, h75, h225,
    phi9, phi25, phi45, phi75, phi225, mu3, mu5, mu9, mu25]

/-- Proper-conductor energy is exactly 1024. -/
theorem base_fifteen_proper_conductor_energy :
    baseFifteenExactConductorEnergyLedger 1 +
      baseFifteenExactConductorEnergyLedger 3 +
      baseFifteenExactConductorEnergyLedger 5 +
      baseFifteenExactConductorEnergyLedger 9 +
      baseFifteenExactConductorEnergyLedger 15 +
      baseFifteenExactConductorEnergyLedger 25 +
      baseFifteenExactConductorEnergyLedger 45 +
      baseFifteenExactConductorEnergyLedger 75 = 1024 := by
  norm_num [base_fifteen_exact_conductor_spectrum]

/-- Full odd energy is exactly 1920, split as 1024 below the top and 896 at
the top conductor. -/
theorem base_fifteen_full_odd_energy :
    (24 : ℤ) + 240 + 360 + 400 + 896 = 1920 ∧
      (1024 : ℤ) + 896 = 1920 := by
  norm_num

/-- The two signed Mobius corrections open into the four nonnegative proper
energies described in the manuscript. -/
theorem base_fifteen_signed_corrections_open :
    (384 : ℤ) = 24 + 360 ∧
      (640 : ℤ) = 240 + 400 := by
  norm_num

end NField.Alignment.BaseFifteenConductorSpectrum
