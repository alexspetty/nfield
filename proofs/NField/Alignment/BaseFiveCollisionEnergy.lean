/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryFiberCentering

/-! # Exact energy of the actual base-five centered collision table -/

noncomputable section
namespace NField.Alignment.BaseFiveCollisionEnergy
open scoped BigOperators
open CollisionCharacterStructure CenteredCollisionSum NeutralityTheorem
  PrimeCarryEnergyBridge PrimeCarryFiberCentering PrimeSquareBoundaryFlux
  PrimeSquareCollisionWindow CollisionFluctuationSum

theorem actual_energy_eq_column_sum {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    [NeZero (allLagModulus p 1)] (hp : p.Prime) :
    primeCarryEnergy hp = ∑ u : UnitClass p, ∑ q : Fin p,
      ‖primeCarryCentered hp (primeFiberCoordinate hp u q)‖ ^ 2 := by
  change (∑ a : UnitClass (allLagModulus p 1), ‖primeCarryCentered hp a‖ ^ 2) = _
  rw [← Fintype.sum_fiberwise (coarseUnitReduction p 1)]
  apply Finset.sum_congr rfl
  intro u _
  exact (Equiv.sum_comp (primeFiberEquiv hp u)
    (fun a => ‖primeCarryCentered hp a.val‖ ^ 2)).symm

theorem base_five_actual_collision_energy :
    primeCarryEnergy (by decide : Nat.Prime 5) = 48 := by
  have hp : Nat.Prime 5 := by decide
  letI : NeZero (allLagModulus 5 1) := ⟨by decide⟩
  change primeCarryEnergy hp = 48
  rw [actual_energy_eq_column_sum]
  rw [← Equiv.sum_comp (lowerFirstWindowEquiv hp)
    (fun u => ∑ q : Fin 5,
      ‖primeCarryCentered hp
        (primeFiberCoordinate hp u q)‖ ^ 2)]
  change (∑ i : Fin 4, ∑ q : Fin 5,
    ‖primeCarryCentered hp
      (primeFiberCoordinate hp (lowerFirstWindowUnit hp i) q)‖ ^ 2) = 48
  change (∑ i : Fin 4, ∑ q : Fin 5,
    ‖(fluctuationTable 5 (primeFiberCoordinate hp (lowerFirstWindowUnit hp i) q).val.val : ℂ) +
      ((5 - (primeFiberCoordinate hp (lowerFirstWindowUnit hp i) q).val.val % 5 : ℕ) : ℂ) / 5‖ ^ 2) = 48
  simp_rw [primeFiberCoordinate_val, lowerFirstWindowUnit_val]
  have hcell (i : Fin 4) (q : Fin 5) :
      ‖(fluctuationTable 5 (firstWindowNat (p := 5) i + 5 * q.val) : ℂ) +
        ((5 - (firstWindowNat (p := 5) i + 5 * q.val) % 5 : ℕ) : ℂ) / 5‖ ^ 2 =
      ((((fluctuationTable 5 (firstWindowNat (p := 5) i + 5 * q.val) : ℚ) +
        ((5 - (firstWindowNat (p := 5) i + 5 * q.val) % 5 : ℕ) : ℚ) / 5) ^ 2 : ℚ) : ℝ) := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
    ring
  simp_rw [hcell]
  have hcalc : (∑ i : Fin 4, ∑ q : Fin 5,
      ((fluctuationTable 5 (firstWindowNat (p := 5) i + 5 * q.val) : ℚ) +
        ((5 - (firstWindowNat (p := 5) i + 5 * q.val) % 5 : ℕ) : ℚ) / 5) ^ 2) = 48 := by
    decide +kernel
  exact_mod_cast hcalc

end NField.Alignment.BaseFiveCollisionEnergy
