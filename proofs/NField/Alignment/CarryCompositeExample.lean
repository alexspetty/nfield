/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenActualEnergy
import NField.Alignment.TerminalCarrySource

/-! # The actual base-fifteen primitive moment, population, and mean -/

noncomputable section
namespace NField.Alignment.CarryCompositeExample
open scoped BigOperators Classical
open CollisionCharacterStructure CarryBoundarySpectra PrimitiveOddBoundaryMean
  ConductorBoundaryLedger BaseFifteenActualEnergy ExactConductorEnergy TerminalCarrySource

local instance : Fact (1 < 225) := ⟨by decide⟩

theorem base_fifteen_weight_eq : digitWeight = terminalDigitWeight 15 2 := by
  funext x
  simp [digitWeight, digitWeightZ, terminalDigitWeight]

theorem primitiveMoment_eq_topEnergy {m : ℕ} [NeZero m] (μ : UnitClass m → ℂ) :
    primitiveOddBoundaryMomentReal μ = exactConductorEnergy m μ := by
  unfold primitiveOddBoundaryMomentReal exactConductorEnergy
  apply Finset.sum_congr
  · ext χ
    simp [DirichletCharacter.IsPrimitive, and_comm]
  · intro χ _
    rfl

/-- Title: `The actual base fifteen terminal boundary has primitive moment eight hundred ninety six`. -/
theorem actual_base_fifteen_moment :
    primitiveOddBoundaryMomentReal (unitBoundarySignal (terminalDigitWeight 15 2)) = 896 := by
  have h := actual_digit_energy_split.2.1
  rw [base_fifteen_weight_eq] at h
  rw [primitiveMoment_eq_topEnergy]
  exact h

set_option maxRecDepth 4000 in
/-- Title: `There are exactly thirty two primitive odd characters modulo two hundred twenty five`. -/
theorem actual_base_fifteen_population : primitiveOddCharacterCount 225 = 32 := by
  have h := primitiveOddKernel_one_eq_count (m := 225)
  rw [primitiveOddKernel_congruenceFormula] at h
  have hd : Nat.divisors 225 = ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ) := by decide
  have hm : ∀ k ∈ ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ),
      ArithmeticFunction.moebius k =
        if k = 1 ∨ k = 15 then 1 else if k = 3 ∨ k = 5 then -1 else 0 := by decide +kernel
  have hv : (- (1 : UnitClass 225)).val.val = 224 := by decide
  have hphi : ∀ k ∈ ({15, 45, 75, 225} : Finset ℕ),
      k.totient = if k = 15 then 8 else if k = 45 then 24 else if k = 75 then 40 else 120 := by decide
  norm_num [hd, residueCongruent, hv, ZMod.val_one, hm, hphi, Nat.ModEq] at h
  exact_mod_cast h.symm

/-- Title: `The actual base fifteen terminal boundary mean is twenty eight`. -/
theorem actual_base_fifteen_mean :
    primitiveOddBoundaryMomentReal (unitBoundarySignal (terminalDigitWeight 15 2)) /
      primitiveOddCharacterCount 225 = 28 := by
  rw [actual_base_fifteen_moment, actual_base_fifteen_population]
  norm_num

end NField.Alignment.CarryCompositeExample
