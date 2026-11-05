/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerFullOrbitBoundary

/-! # Primitive characters at an odd prime square are not self-conjugate -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.PrimeSquareCharacterPairs
open CollisionCharacterStructure PrimitiveOddBoundaryMean PrimePowerFullOrbitBoundary

theorem self_inverse_factorsThrough {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p ^ 2)) (hχ : χ⁻¹ = χ) :
    χ.FactorsThrough p := by
  let hd : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  let π := ZMod.unitsMap hd
  have hcard : Fintype.card π.ker = p := by
    simpa [π, hd] using prime_unitsMap_kernel_card (e := 2) hp (by decide)
  have huPow : u ^ p = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one (x := (⟨u, hu⟩ : π.ker)))
    simpa only [hcard, Subgroup.coe_pow, Subgroup.coe_one] using h
  have hpval : (χ u.val) ^ p = 1 := by
    have hv : u.val ^ p = 1 := congrArg Units.val huPow
    rw [← map_pow, hv, map_one]
  have hsq : χ * χ = 1 := by
    calc
      χ * χ = χ * χ⁻¹ := by rw [hχ]
      _ = 1 := mul_inv_cancel χ
  have htwo : (χ u.val) ^ 2 = 1 := by
    have h := congrArg (fun ψ : Character (p ^ 2) => ψ u.val) hsq
    simpa [pow_two, MulChar.one_apply u.isUnit] using h
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpodd
  have hpk : p = 2 * k + 1 := by omega
  have hoddval : (χ u.val) ^ (2 * k + 1) = 1 :=
    (congrArg (fun n : ℕ => (χ u.val) ^ n) hpk.symm).trans hpval
  rw [pow_add, pow_mul, htwo, one_pow, pow_one, one_mul] at hoddval
  change χ.toUnitHom u = 1
  apply Units.ext
  exact hoddval

theorem primitive_ne_inverse {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p ^ 2))
    (hprim : χ.IsPrimitive) : χ⁻¹ ≠ χ := by
  intro hχ
  have hfac := self_inverse_factorsThrough hp hpodd χ hχ
  have hn := (nonprimitive_iff_factorsThrough_previous hp (by decide : 2 ≤ 2) χ).mpr
    (by simpa using hfac)
  exact hn hprim

theorem primitive_ne_conjugate {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p ^ 2))
    (hprim : χ.IsPrimitive) : star χ ≠ χ := by
  rw [MulChar.star_eq_inv]
  exact primitive_ne_inverse hp hpodd χ hprim

end NField.Alignment.PrimeSquareCharacterPairs
