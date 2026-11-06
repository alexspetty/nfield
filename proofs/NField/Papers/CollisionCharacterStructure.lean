/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterStructure
import NField.Papers.BinDerangements

/-!
# The Character Structure of the Collision Fluctuation

## Coverage

Finite collision fluctuations have an invertible Dirichlet-character transform
with the stated Parseval normalization and conjugation law. The theorem
applies to any finite packet of unit residues and complex weights. The cutoff
question remains open.

## Scope and assumptions

The character theorem applies to an arbitrary finite packet of unit residues
and complex weights, with Parseval factor `Nat.totient b`. A cutoff, lag or
weight `Delta / p^s` supplies finite data for this theorem; it does not turn
it into an infinite-series convergence statement. The displayed decimal table
is a numerical evaluation, not floating-point Lean data. The cutoff question
remains open.
-/

namespace NField.Papers.CollisionCharacterStructure

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangementsClosure

/-- Exact displayed floor-difference formula for the digit partition. -/
theorem exact_bin_cardinality {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (d : Fin b) :
    (NField.Alignment.SpectralPower.binSet
      (NField.Alignment.SpectralPower.primeDigitWord
        b p (by omega) hp.pos) d).card =
      ((d.val + 1) * p) / b - (d.val * p) / b -
        (if d.val = b - 1 then 1 else 0) :=
  NField.Papers.BinDerangements.exact_bin_cardinality hb2 hp hbp d

/-- Exact interval-to-congruence conjugation used in the constructive-mean
proof. -/
theorem bin_conjugation {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    NField.CollisionDefinition.digitBin b p r.val =
        NField.CollisionDefinition.digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b = ((b : ZMod p) * s).val % b :=
  NField.Papers.BinDerangements.bin_conjugation hb hp hbp r s

/-- Exact collision-congruence identity for the intrinsic prime word. -/
theorem collision_congruence {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) (hg0 : g ≠ 0) :
    NField.Alignment.PhaseFilteredRamanujan.collisionCount
        (NField.Alignment.SpectralPower.primeDigitWord
          b p hb hp.pos) g =
      NField.Alignment.BinDerangements.transformedCollisionCount b p g :=
  NField.Papers.BinDerangements.collision_congruence hb hp hbp g hg0

/-- The actual constructive multiplier set has the displayed cardinality and
collision mass. -/
theorem constructive_set_certificate {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    (constructiveMultiplierSet b p (by omega) hp).card =
        b * (Q - 1) + R ∧
      (∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g) =
          Q * (b * (Q - 1) + 2 * R) :=
  NField.Papers.BinDerangements.constructive_set_certificate
    hb2 hp hbp1 hdivision hR

/-- The average over the actual constructive multiplier set is the exact
displayed rational mean. -/
theorem constructive_mean {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    ((∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℚ) /
        ((constructiveMultiplierSet b p (by omega) hp).card : ℚ) =
      constructiveMeanValue b Q R :=
  NField.Papers.BinDerangements.actual_constructive_mean
    hb2 hp hbp1 hdivision hR

/-- Exact collision deviation at the power multiplier `[b^ell]_p`. -/
theorem power_lag_deviation (b p Q R ell : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) :
    collisionDeviation b p Q R hb hp (powerMultiplier b p ell) =
      (NField.Alignment.PhaseFilteredRamanujan.collisionCount
        (NField.Alignment.SpectralPower.primeDigitWord
          b p hb hp.pos) (powerMultiplier b p ell) : ℚ) -
        NField.Alignment.BinDerangementsClosure.constructiveMeanValue b Q R :=
  collisionDeviation_at_power b p Q R ell hb hp

/-- The identity multiplier remains valid in the centered deviation. -/
theorem identity_lag_deviation (b p Q R : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) :
    collisionDeviation b p Q R hb hp 1 =
      (p - 1 : ℕ) -
        NField.Alignment.BinDerangementsClosure.constructiveMeanValue b Q R :=
  collisionDeviation_at_identity b p Q R hb hp

/-- Exact orthogonality relation used in inversion and Parseval. -/
theorem character_orthogonality {b : ℕ} [NeZero b]
    (r t : UnitClass b) :
    ∑ χ : Character b, star (χ r.val) * χ t.val =
      if r = t then (b.totient : ℂ) else 0 :=
  unit_character_orthogonality r t

/-- Exact forward transform after partitioning a finite packet by residue
class. -/
theorem finite_packet_forward {b : ℕ} [NeZero b]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ)
    (χ : Character b) :
    packetCharacterComponent residue weight χ =
      characterTransform (residueStream residue weight) χ :=
  packetCharacterComponent_eq_transform residue weight χ

/-- Exact inverse character transform. -/
theorem finite_character_inverse {b : ℕ} [NeZero b]
    (F : UnitClass b → ℂ) (r : UnitClass b) :
    inverseCharacterTransform (characterTransform F) r = F r :=
  inverse_characterTransform F r

/-- The finite character coordinates determine the residue stream uniquely. -/
theorem finite_transform_injective {b : ℕ} [NeZero b] :
    Function.Injective (characterTransform (b := b)) :=
  characterTransform_injective

/-- The principal character component is the total signal. -/
theorem principal_component {b : ℕ} [NeZero b]
    (F : UnitClass b → ℂ) :
    characterTransform F 1 = ∑ r : UnitClass b, F r :=
  principal_character_component F

/-- The principal component of a grouped packet is its total weight. -/
theorem finite_packet_principal {b : ℕ} [NeZero b]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ) :
    packetCharacterComponent residue weight 1 = ∑ i : ι, weight i :=
  packet_principal_component residue weight

/-- The residue streams sum to the total packet weight. -/
theorem finite_residue_stream_total {b : ℕ} [NeZero b]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ) :
    ∑ r : UnitClass b, residueStream residue weight r =
      ∑ i : ι, weight i :=
  residueStream_total residue weight

/-- Exact squared-magnitude Parseval identity. -/
theorem finite_parseval {b : ℕ} [NeZero b]
    (F : UnitClass b → ℂ) :
    ∑ χ : Character b, ‖characterTransform F χ‖ ^ 2 =
      b.totient * ∑ r : UnitClass b, ‖F r‖ ^ 2 :=
  character_parseval F

/-- Exact conjugate pairing for a conjugated finite signal. -/
theorem conjugate_pairing {b : ℕ} [NeZero b]
    (F : UnitClass b → ℂ) (χ : Character b) :
    characterTransform (fun r => star (F r)) (star χ) =
      star (characterTransform F χ) :=
  characterTransform_conjugate F χ

/-- Equal magnitudes for conjugate characters when the finite signal is real. -/
theorem conjugate_pairing_equal_magnitude {b : ℕ} [NeZero b]
    (F : UnitClass b → ℂ) (hF : ∀ r, star (F r) = F r)
    (χ : Character b) :
    ‖characterTransform F (star χ)‖ = ‖characterTransform F χ‖ :=
  characterTransform_norm_star_character_of_real F hF χ

/-- The complex character group has exactly `Nat.totient b` elements. -/
theorem character_count {b : ℕ} [NeZero b] :
    Fintype.card (Character b) = b.totient :=
  character_card_eq_totient

/-- The unit-class side of the transform also has exactly `phi(b)`
coordinates. -/
theorem unit_class_count {b : ℕ} [NeZero b] :
    Fintype.card (UnitClass b) = b.totient :=
  unitClass_card_eq_totient

/-- The manuscript's base-ten transform has exactly four coordinates. -/
theorem decimal_character_count : Fintype.card (Character 10) = 4 := by
  calc
    Fintype.card (Character 10) = Nat.totient 10 := character_card_eq_totient
    _ = 4 := by decide

/-- In base ten there are four unit classes, and the class of three generates
all four. -/
theorem decimal_unit_structure :
    Fintype.card (UnitClass 10) = 4 ∧ orderOf decimalUnitThree = 4 := by
  constructor
  · rw [unitClass_card_eq_totient]
    decide
  · exact decimalUnitThree_order

#check unit_character_orthogonality
#check exact_bin_cardinality
#check bin_conjugation
#check collision_congruence
#check constructive_set_certificate
#check constructive_mean
#check power_lag_deviation
#check identity_lag_deviation
#check character_orthogonality
#check finite_packet_forward
#check finite_character_inverse
#check finite_transform_injective
#check principal_component
#check finite_packet_principal
#check finite_residue_stream_total
#check finite_parseval
#check conjugate_pairing
#check conjugate_pairing_equal_magnitude
#check character_count
#check unit_class_count
#check decimal_character_count
#check decimal_unit_structure

end NField.Papers.CollisionCharacterStructure
