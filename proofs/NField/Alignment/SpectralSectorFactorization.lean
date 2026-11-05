/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralCharacterDistributions

/-! # The full odd sector and its actual primitive occupancy -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SpectralSectorFactorization
open scoped BigOperators Classical
open CollisionCharacterStructure SpectralCharacterPairs
open SpectralCharacterDistributions

def primitiveInOddEquiv (b : ℕ) :
    {χ : OddFamily b // χ.val.IsPrimitive} ≃ PrimitiveOddFamily b where
  toFun χ := ⟨χ.val.val, χ.property, χ.val.property⟩
  invFun χ := ⟨⟨χ.val, χ.property.2⟩, χ.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def extendMass (b : ℕ) (w : PrimitiveOddFamily b → ℝ) (χ : OddFamily b) : ℝ :=
  if h : χ.val.IsPrimitive then w ⟨χ.val, h, χ.property⟩ else 0

theorem sum_extension (b : ℕ) (w : PrimitiveOddFamily b → ℝ) :
    ∑ χ : OddFamily b, extendMass b w χ = ∑ χ, w χ := by
  rw [← Equiv.sum_comp (primitiveInOddEquiv b)]
  apply Finset.sum_congr_set {χ : OddFamily b | χ.val.IsPrimitive}
    (extendMass b w) (fun χ => w (primitiveInOddEquiv b χ))
  · intro χ hχ
    change χ.val.IsPrimitive at hχ
    simp [extendMass, hχ, primitiveInOddEquiv]
  · intro χ hχ
    change ¬χ.val.IsPrimitive at hχ
    simp [extendMass, hχ]

def oddPrimeEnergy (b : ℕ) (X : ℝ) : ℝ :=
  ∑ χ : OddFamily b, ‖primeSum b X χ.val‖ ^ 2

def oddPrimeMass (b : ℕ) (X : ℝ) (χ : OddFamily b) : ℝ :=
  ‖primeSum b X χ.val‖ ^ 2 / oddPrimeEnergy b X

def occupancy (b : ℕ) (X : ℝ) : ℝ :=
  ∑ χ : PrimitiveOddFamily b, oddPrimeMass b X ⟨χ.val, χ.property.2⟩

theorem occupancy_ratio (b : ℕ) (X : ℝ) :
    occupancy b X = primeEnergy b X / oddPrimeEnergy b X := by
  simp only [occupancy, oddPrimeMass, ← Finset.sum_div, primeEnergy]

theorem restricted_prime_mass (b : ℕ) (X : ℝ) (h : primeEnergy b X ≠ 0)
    (χ : PrimitiveOddFamily b) :
    oddPrimeMass b X ⟨χ.val, χ.property.2⟩ = occupancy b X * primeMass b X χ := by
  rw [occupancy_ratio]
  unfold oddPrimeMass primeMass
  field_simp

def oddScaledOverlap (b : ℕ) [NeZero b] [NeZero (b ^ 2)] (X : ℝ) : ℝ :=
  (Fintype.card (OddFamily b) : ℝ) *
    ∑ χ : OddFamily b, extendMass b (collisionMass b) χ * oddPrimeMass b X χ

theorem actual_sector_factorization {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (X : ℝ) (hprime : primeEnergy b X ≠ 0) :
    oddScaledOverlap b X =
      ((Fintype.card (OddFamily b) : ℝ) / Fintype.card (PrimitiveOddFamily b)) *
        occupancy b X * scaledOverlap b X := by
  have hsum : (∑ χ : OddFamily b, extendMass b (collisionMass b) χ * oddPrimeMass b X χ) =
      ∑ χ : PrimitiveOddFamily b, collisionMass b χ * oddPrimeMass b X ⟨χ.val, χ.property.2⟩ := by
    have hpoint (χ : OddFamily b) :
        extendMass b (collisionMass b) χ * oddPrimeMass b X χ =
          extendMass b (fun ψ => collisionMass b ψ * oddPrimeMass b X ⟨ψ.val, ψ.property.2⟩) χ := by
      by_cases hχ : χ.val.IsPrimitive <;> simp [extendMass, hχ]
    simp_rw [hpoint]
    exact sum_extension b _
  have hcard : (Fintype.card (PrimitiveOddFamily b) : ℝ) ≠ 0 := by
    haveI := family_nonempty hb hbodd
    exact_mod_cast Fintype.card_ne_zero
  unfold oddScaledOverlap scaledOverlap
  rw [hsum]
  simp_rw [restricted_prime_mass b X hprime]
  rw [show (∑ χ, collisionMass b χ * (occupancy b X * primeMass b X χ)) =
      occupancy b X * ∑ χ, collisionMass b χ * primeMass b X χ by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro χ _; ring]
  field_simp

end NField.Alignment.SpectralSectorFactorization
