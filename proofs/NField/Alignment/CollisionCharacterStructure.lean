/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BinDerangementsClosure
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Character structure of the collision fluctuation

Reusable finite character-transform proofs for the Lean companion to
"The Character Structure of the Collision Fluctuation".
-/

namespace NField.Alignment.CollisionCharacterStructure

open scoped BigOperators ComplexConjugate
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangementsClosure

/-- A unit residue class modulo the base. -/
abbrev UnitClass (b : ℕ) := (ZMod b)ˣ

/-- A complex Dirichlet character modulo the base. -/
abbrev Character (b : ℕ) := DirichletCharacter ℂ b

variable {b : ℕ} [NeZero b]

/-- The finite collision deviation after centering by the exact constructive
mean. -/
def collisionDeviation (b p Q R : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) (g : ZMod p) : ℚ :=
  (collisionCount (primeDigitWord b p hb hp.pos) g : ℚ) -
    constructiveMeanValue b Q R

/-- The multiplier attached to a positive power lag. -/
def powerMultiplier (b p ell : ℕ) : ZMod p :=
  (b ^ ell : ℕ)

/-- The displayed power-lag deviation is the collision count at
`[b^ell]_p` minus the exact constructive mean. -/
theorem collisionDeviation_at_power (b p Q R ell : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) :
    collisionDeviation b p Q R hb hp (powerMultiplier b p ell) =
      (collisionCount (primeDigitWord b p hb hp.pos)
        (powerMultiplier b p ell) : ℚ) - constructiveMeanValue b Q R :=
  rfl

/-- The identity multiplier remains in the deviation domain and contributes
all `p-1` assigned residues. -/
theorem collisionDeviation_at_identity (b p Q R : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) :
    collisionDeviation b p Q R hb hp 1 =
      (p - 1 : ℕ) - constructiveMeanValue b Q R := by
  rw [collisionDeviation, collisionCount_one, prime_assignedMass]

/-- The unit residue classes have cardinality `phi(b)`. -/
theorem unitClass_card_eq_totient :
    Fintype.card (UnitClass b) = b.totient :=
  ZMod.card_units_eq_totient b

/-- The residue class of three is a unit modulo ten. -/
def decimalUnitThree : UnitClass 10 :=
  ZMod.unitOfCoprime 3 (by norm_num)

/-- Three generates the four unit classes modulo ten. -/
theorem decimalUnitThree_order : orderOf decimalUnitThree = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  constructor
  · decide
  · intro q hq hq0
    interval_cases q <;> decide

/-- Fourier coordinate of a signal on the unit residue classes. -/
noncomputable def characterTransform
    (F : UnitClass b → ℂ) (χ : Character b) : ℂ :=
  ∑ r : UnitClass b, χ r.val * F r

/-- Reconstruction of a residue stream from all character coordinates. -/
noncomputable def inverseCharacterTransform
    (H : Character b → ℂ) (r : UnitClass b) : ℂ :=
  (b.totient : ℂ)⁻¹ *
    ∑ χ : Character b, star (χ r.val) * H χ

/-- Residue stream obtained by grouping an arbitrary finite packet by its
unit class. -/
noncomputable def residueStream {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ)
    (r : UnitClass b) : ℂ :=
  ∑ i : ι, if residue i = r then weight i else 0

/-- Character-weighted component of the same finite packet. -/
noncomputable def packetCharacterComponent {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ)
    (χ : Character b) : ℂ :=
  ∑ i : ι, χ (residue i).val * weight i

/-- Partitioning a finite packet by unit residue class gives the forward
character transform exactly. -/
theorem packetCharacterComponent_eq_transform
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ)
    (χ : Character b) :
    packetCharacterComponent residue weight χ =
      characterTransform (residueStream residue weight) χ := by
  classical
  unfold packetCharacterComponent characterTransform residueStream
  symm
  calc
    (∑ r : UnitClass b,
        χ r.val * ∑ i : ι, if residue i = r then weight i else 0) =
      ∑ r : UnitClass b, ∑ i : ι,
        χ r.val * (if residue i = r then weight i else 0) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ r : UnitClass b,
        χ r.val * (if residue i = r then weight i else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, χ (residue i).val * weight i := by
          apply Finset.sum_congr rfl
          intro i _
          simp

/-- Character orthogonality on the unit residue classes, in the precise
conjugated form used by inversion and Parseval. -/
theorem unit_character_orthogonality (r t : UnitClass b) :
    ∑ χ : Character b, star (χ r.val) * χ t.val =
      if r = t then (b.totient : ℂ) else 0 := by
  calc
    (∑ χ : Character b, star (χ r.val) * χ t.val) =
      ∑ χ : Character b, χ r.val⁻¹ * χ t.val := by
        apply Finset.sum_congr rfl
        intro χ _
        congr 1
        calc
          star (χ r.val) = ((χ : MulChar (ZMod b) ℂ)⁻¹) r.val :=
            MulChar.star_apply' (χ : MulChar (ZMod b) ℂ) r.val
          _ = χ (r⁻¹ : UnitClass b).val := by
            rw [MulChar.inv_apply, Ring.inverse_unit]
          _ = χ r.val⁻¹ := by rw [ZMod.inv_coe_unit]
    _ = if r.val = t.val then (b.totient : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit t.val
    _ = if r = t then (b.totient : ℂ) else 0 := by
      simp [Units.ext_iff]

/-- The number of complex characters equals the number of unit classes. -/
theorem character_card_eq_totient :
    Fintype.card (Character b) = b.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ b

/-- Exact inverse transform on every unit-class signal. -/
theorem inverse_characterTransform (F : UnitClass b → ℂ)
    (r : UnitClass b) :
    inverseCharacterTransform (characterTransform F) r = F r := by
  classical
  have htot : (b.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos b)).ne'
  unfold inverseCharacterTransform characterTransform
  calc
    (b.totient : ℂ)⁻¹ *
        ∑ χ : Character b,
          star (χ r.val) * ∑ t : UnitClass b, χ t.val * F t =
      (b.totient : ℂ)⁻¹ *
        ∑ t : UnitClass b,
          (∑ χ : Character b, star (χ r.val) * χ t.val) * F t := by
            congr 1
            calc
              (∑ χ : Character b,
                  star (χ r.val) * ∑ t : UnitClass b, χ t.val * F t) =
                ∑ χ : Character b, ∑ t : UnitClass b,
                  star (χ r.val) * (χ t.val * F t) := by
                    apply Finset.sum_congr rfl
                    intro χ _
                    rw [Finset.mul_sum]
              _ = ∑ t : UnitClass b, ∑ χ : Character b,
                  star (χ r.val) * (χ t.val * F t) := by
                    rw [Finset.sum_comm]
              _ = ∑ t : UnitClass b,
                  (∑ χ : Character b, star (χ r.val) * χ t.val) * F t := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro χ _
                    ring
    _ = (b.totient : ℂ)⁻¹ *
        ∑ t : UnitClass b,
          (if r = t then (b.totient : ℂ) else 0) * F t := by
            simp_rw [unit_character_orthogonality]
    _ = (b.totient : ℂ)⁻¹ * ((b.totient : ℂ) * F r) := by simp
    _ = F r := by field_simp

/-- No information is lost: equal character coordinates force equal residue
streams. -/
theorem characterTransform_injective :
    Function.Injective (characterTransform (b := b)) := by
  intro F G h
  funext r
  rw [← inverse_characterTransform F r,
    ← inverse_characterTransform G r, h]

/-- The principal coordinate is the total finite fluctuation. -/
theorem principal_character_component (F : UnitClass b → ℂ) :
    characterTransform F 1 = ∑ r : UnitClass b, F r := by
  unfold characterTransform
  apply Finset.sum_congr rfl
  intro r _
  rw [MulChar.one_apply r.isUnit, one_mul]

/-- The total of all residue streams is the total weight of the original
finite packet. -/
theorem residueStream_total {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ) :
    ∑ r : UnitClass b, residueStream residue weight r = ∑ i : ι, weight i := by
  classical
  unfold residueStream
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Consequently the principal packet component is exactly its unweighted
total. -/
theorem packet_principal_component {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass b) (weight : ι → ℂ) :
    packetCharacterComponent residue weight 1 = ∑ i : ι, weight i := by
  rw [packetCharacterComponent_eq_transform,
    principal_character_component, residueStream_total]

/-- Conjugating both the signal and the character conjugates the transform.
This is the exact finite form behind the manuscript's conjugate pairing. -/
theorem characterTransform_conjugate
    (F : UnitClass b → ℂ) (χ : Character b) :
    characterTransform (fun r => star (F r)) (star χ) =
      star (characterTransform F χ) := by
  classical
  unfold characterTransform
  change (∑ r : UnitClass b, (star χ) r.val * star (F r)) =
    (starRingEnd ℂ) (∑ r : UnitClass b, χ r.val * F r)
  rw [map_sum (starRingEnd ℂ)]
  apply Finset.sum_congr rfl
  intro r _
  rw [MulChar.star_apply, map_mul]
  simp only [starRingEnd_apply]

/-- A real-valued residue signal has conjugate character coordinates in
conjugate pairs. -/
theorem characterTransform_star_character_of_real
    (F : UnitClass b → ℂ) (hF : ∀ r, star (F r) = F r)
    (χ : Character b) :
    characterTransform F (star χ) = star (characterTransform F χ) := by
  simpa only [hF] using characterTransform_conjugate F χ

/-- Conjugate character coordinates of a real-valued signal have equal
magnitudes. -/
theorem characterTransform_norm_star_character_of_real
    (F : UnitClass b → ℂ) (hF : ∀ r, star (F r) = F r)
    (χ : Character b) :
    ‖characterTransform F (star χ)‖ = ‖characterTransform F χ‖ := by
  rw [characterTransform_star_character_of_real F hF χ, norm_star]

/-- Complex-valued Parseval identity for the finite character transform. -/
theorem character_parseval_complex (F : UnitClass b → ℂ) :
    ∑ χ : Character b,
        star (characterTransform F χ) * characterTransform F χ =
      (b.totient : ℂ) * ∑ r : UnitClass b, star (F r) * F r := by
  classical
  have hstar (χ : Character b) :
      star (∑ r : UnitClass b, χ r.val * F r) =
        ∑ r : UnitClass b, star (χ r.val) * star (F r) := by
    change (starRingEnd ℂ) (∑ r : UnitClass b, χ r.val * F r) = _
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_mul]
    simp only [starRingEnd_apply]
  unfold characterTransform
  simp_rw [hstar]
  calc
    (∑ χ : Character b,
        (∑ r : UnitClass b, star (χ r.val) * star (F r)) *
          ∑ t : UnitClass b, χ t.val * F t) =
      ∑ χ : Character b, ∑ r : UnitClass b, ∑ t : UnitClass b,
        (star (χ r.val) * χ t.val) * (star (F r) * F t) := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          ring
    _ = ∑ r : UnitClass b, ∑ t : UnitClass b,
        (∑ χ : Character b, star (χ r.val) * χ t.val) *
          (star (F r) * F t) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_mul]
    _ = ∑ r : UnitClass b, ∑ t : UnitClass b,
        (if r = t then (b.totient : ℂ) else 0) *
          (star (F r) * F t) := by
            simp_rw [unit_character_orthogonality]
    _ = (b.totient : ℂ) *
        ∑ r : UnitClass b, star (F r) * F r := by
          simp [Finset.mul_sum]

/-- Parseval in the manuscript's squared-magnitude form. -/
theorem character_parseval (F : UnitClass b → ℂ) :
    ∑ χ : Character b, ‖characterTransform F χ‖ ^ 2 =
      b.totient * ∑ r : UnitClass b, ‖F r‖ ^ 2 := by
  simp_rw [Complex.sq_norm]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  exact character_parseval_complex F

end NField.Alignment.CollisionCharacterStructure
