/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CenteredCollisionClosure
import NField.Alignment.TheStructureThatSurvives
import NField.Alignment.PrimeSquareBoundaryFlux

/-! # Literal finite sum and raw-character clauses in the centered manuscript -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CenteredSourceDetails

open scoped BigOperators ComplexConjugate
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower
open NField.Alignment.BinDerangements
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.TheStructureThatSurvives

/-- Title: `Nonidentity collision mass counts distinct pairs within each bin`. -/
theorem nonidentity_collision_sum {p κ : ℕ} [NeZero p] (hp : p.Prime)
    (word : ZMod p → Option (Fin κ)) (hzero : word 0 = none) :
    (∑ g ∈ (Finset.univ.erase 1 : Finset (ZMod p)), collisionCount word g) =
      ∑ d : Fin κ, (binSet word d).card * ((binSet word d).card - 1) := by
  classical
  have h := Finset.sum_erase_add Finset.univ (collisionCount word)
    (Finset.mem_univ (1 : ZMod p))
  rw [collisionCount_one, collisionCount_sum_rule hp word hzero] at h
  have hbin (n : ℕ) : n * (n - 1) + n = n ^ 2 := by
    cases n <;> simp <;> ring
  have hsum : (∑ d : Fin κ, (binSet word d).card * ((binSet word d).card - 1)) +
      assignedMass word = binSquareMass word := by
    rw [assignedMass, ← Finset.sum_add_distrib]
    simp only [hbin, binSquareMass]
  omega

/-- Title: `The raw table principal character coefficient is minus one half`. -/
theorem raw_table_principal_coefficient {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    collisionCoefficient (allLagUnitTable b ell) 1 = -1 / 2 := by
  unfold collisionCoefficient finiteCoefficient
  simp only [MulChar.one_apply_coe, star_one, mul_one]
  exact allLagUnitTable_grand_mean hb hell

/-- Title: `Every nonprincipal even character vanishes in the raw table`. -/
theorem raw_table_nonprincipal_even_zero {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (χ : Character (allLagModulus b ell))
    (heven : χ.Even) (hne : χ ≠ 1) :
    collisionCoefficient (allLagUnitTable b ell) χ = 0 := by
  have hchar := NField.Alignment.PrimeSquareBoundaryFlux.unitCharacterSum_eq_zero χ hne
  have hstar : (∑ a : UnitClass (allLagModulus b ell), star (χ a.val)) = 0 := by
    rw [← star_sum, hchar, star_zero]
  have h := halfCenteredUnitTable_evenCoefficient_zero hb hell χ heven
  unfold collisionCoefficient finiteCoefficient halfCenteredUnitTable at h
  unfold collisionCoefficient finiteCoefficient
  simpa only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hstar,
    mul_zero, add_zero] using h

end NField.Alignment.CenteredSourceDetails
