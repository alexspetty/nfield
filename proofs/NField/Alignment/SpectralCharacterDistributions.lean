/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralCharacterPairs
import NField.Alignment.TheCollisionSpectrum

/-! # Actual collision and finite prime distributions, with conjugate masses -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SpectralCharacterDistributions
open scoped BigOperators
open CollisionCharacterStructure CenteredCollisionSum CollisionTransformStrip
open TheCollisionSpectrum SpectralCharacterPairs

local instance (b : ℕ) [NeZero (b ^ 2)] : NeZero (allLagModulus b 1) :=
  ⟨by simpa only [allLagModulus, Nat.reduceAdd] using (NeZero.ne (b ^ 2))⟩

def collisionCoeff (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (χ : Character (b ^ 2)) : ℂ := collisionCoefficient (centeredLagOneSpectrum b) χ

def primeWindow (b : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.range ⌈X⌉₊).filter fun p => p.Prime ∧ b ^ 2 < p

theorem mem_primeWindow (b p : ℕ) (X : ℝ) :
    p ∈ primeWindow b X ↔ p.Prime ∧ b ^ 2 < p ∧ (p : ℝ) < X := by
  simp only [primeWindow, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

def primeSum (b : ℕ) (X : ℝ) (χ : Character (b ^ 2)) : ℂ :=
  ∑ p ∈ primeWindow b X, χ (p : ZMod (b ^ 2)) / (Real.sqrt p : ℂ)

theorem centered_lag_one_real (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (u : UnitClass (b ^ 2)) : star (centeredLagOneSpectrum b u) = centeredLagOneSpectrum b u := by
  simp [centeredLagOneSpectrum, CollisionTransform.centeredCollisionTransform,
    centeredSignal, fiberMean, allLagUnitTable]

theorem collisionCoeff_conjugate (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (χ : Character (b ^ 2)) : collisionCoeff b (star χ) = star (collisionCoeff b χ) := by
  have general {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
      (hF : ∀ a, star (F a) = F a) (ψ : Character q) :
      collisionCoefficient F (star ψ) = star (collisionCoefficient F ψ) := by
    simp [collisionCoefficient, finiteCoefficient, MulChar.star_apply, hF]
  exact general (centeredLagOneSpectrum b) (centered_lag_one_real b) χ

theorem primeSum_conjugate (b : ℕ) (X : ℝ) (χ : Character (b ^ 2)) :
    primeSum b X (star χ) = star (primeSum b X χ) := by
  simp [primeSum, MulChar.star_apply]

def collisionEnergy (b : ℕ) [NeZero b] [NeZero (b ^ 2)] : ℝ :=
  ∑ χ : PrimitiveOddFamily b, ‖collisionCoeff b χ.val‖ ^ 2

def primeEnergy (b : ℕ) (X : ℝ) : ℝ :=
  ∑ χ : PrimitiveOddFamily b, ‖primeSum b X χ.val‖ ^ 2

def collisionMass (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (χ : PrimitiveOddFamily b) : ℝ := ‖collisionCoeff b χ.val‖ ^ 2 / collisionEnergy b

def primeMass (b : ℕ) (X : ℝ) (χ : PrimitiveOddFamily b) : ℝ :=
  ‖primeSum b X χ.val‖ ^ 2 / primeEnergy b X

theorem collisionMass_nonneg (b : ℕ) [NeZero b] [NeZero (b ^ 2)] (χ : PrimitiveOddFamily b) :
    0 ≤ collisionMass b χ :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem primeMass_nonneg (b : ℕ) (X : ℝ) (χ : PrimitiveOddFamily b) :
    0 ≤ primeMass b X χ :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem collisionMass_sum (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (h : collisionEnergy b ≠ 0) : ∑ χ, collisionMass b χ = 1 := by
  simp only [collisionMass, ← Finset.sum_div]
  exact div_self h

theorem primeMass_sum (b : ℕ) (X : ℝ) (h : primeEnergy b X ≠ 0) :
    ∑ χ, primeMass b X χ = 1 := by
  simp only [primeMass, ← Finset.sum_div]
  exact div_self h

theorem collisionMass_conjugate (b : ℕ) [NeZero b] [NeZero (b ^ 2)]
    (χ : PrimitiveOddFamily b) : collisionMass b (conjugate χ) = collisionMass b χ := by
  simp [collisionMass, conjugate, collisionCoeff_conjugate]

theorem primeMass_conjugate (b : ℕ) (X : ℝ) (χ : PrimitiveOddFamily b) :
    primeMass b X (conjugate χ) = primeMass b X χ := by
  simp [primeMass, conjugate, primeSum_conjugate]

def collisionPairMass (b : ℕ) [NeZero b] [NeZero (b ^ 2)] (r : Pairs b) : ℝ :=
  collisionMass b r + collisionMass b (conjugate r)

def primePairMass (b : ℕ) (X : ℝ) (r : Pairs b) : ℝ :=
  primeMass b X r + primeMass b X (conjugate r)

theorem collisionPairMass_sum {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (h : collisionEnergy b ≠ 0) :
    ∑ r, collisionPairMass b r = 1 :=
  pair_mass_sum hb hbodd (collisionMass b) (collisionMass_sum b h)

theorem primePairMass_sum {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (X : ℝ) (h : primeEnergy b X ≠ 0) :
    ∑ r, primePairMass b X r = 1 :=
  pair_mass_sum hb hbodd (primeMass b X) (primeMass_sum b X h)

def scaledOverlap (b : ℕ) [NeZero b] [NeZero (b ^ 2)] (X : ℝ) : ℝ :=
  (Fintype.card (PrimitiveOddFamily b) : ℝ) * ∑ χ, collisionMass b χ * primeMass b X χ

theorem scaledOverlap_pairs {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (X : ℝ) :
    scaledOverlap b X = (Fintype.card (Pairs b) : ℝ) *
      ∑ r, collisionPairMass b r * primePairMass b X r :=
  pair_overlap hb hbodd (collisionMass b) (primeMass b X)
    (collisionMass_conjugate b) (primeMass_conjugate b X)

end NField.Alignment.SpectralCharacterDistributions
