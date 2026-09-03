/-
Author: Alexander S. Petty
-/

import NField.Alignment.CosetFourierReduction

/-!
# Prime coset ordering

This module turns the abstract quotient by the base-generated subgroup into
the concrete ordering by a chosen coset representative times powers of the
base.  The ordering is proved bijective, so the simultaneous Fourier
reduction applies to every actual nonzero prime residue exactly once.
-/

namespace NField.Alignment.PrimeCosetOrdering

open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix

/-- Quotient type of multiplicative base orbits modulo a coprime prime. -/
abbrev PrimeOrbitQuotient {b p : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) :=
  (ZMod p)ˣ ⧸ primeBaseOrbitSubgroup b p hp hpb

/-- The fixed representative selected by the quotient implementation.  No
result depends on which representative is selected. -/
noncomputable def primeOrbitRepresentative {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (C : PrimeOrbitQuotient hp hpb) :
    (ZMod p)ˣ :=
  Quotient.out C

theorem primeOrbitRepresentative_quotient {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (C : PrimeOrbitQuotient hp hpb) :
    (primeOrbitRepresentative hp hpb C : PrimeOrbitQuotient hp hpb) = C := by
  exact Quotient.out_eq C

/-- Actual unit residue in coset `C` at exponent coordinate `r`. -/
noncomputable def primeCosetOrdering {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    PrimeOrbitQuotient hp hpb × Fin (primeBasePeriod b p hp hpb) →
      (ZMod p)ˣ :=
  fun Cr => primeOrbitRepresentative hp hpb Cr.1 *
    (primeBaseUnit b p hp hpb) ^ Cr.2.val

/-- The ordered residue lies in its declared quotient coset. -/
theorem primeCosetOrdering_quotient {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb)
    (r : Fin (primeBasePeriod b p hp hpb)) :
    (primeCosetOrdering hp hpb (C, r) : PrimeOrbitQuotient hp hpb) = C := by
  calc
    (primeCosetOrdering hp hpb (C, r) : PrimeOrbitQuotient hp hpb) =
        (primeOrbitRepresentative hp hpb C : PrimeOrbitQuotient hp hpb) :=
      ((same_primeBaseOrbit_iff hp hpb
        (primeOrbitRepresentative hp hpb C)
        (primeCosetOrdering hp hpb (C, r))).2
          ⟨r.val, r.isLt, by rfl⟩).symm
    _ = C := primeOrbitRepresentative_quotient hp hpb C

/-- Every nonzero prime residue has a coset and a unique exponent in the
canonical range. -/
theorem primeCosetOrdering_surjective {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    Function.Surjective (primeCosetOrdering hp hpb) := by
  intro x
  let C : PrimeOrbitQuotient hp hpb := x
  have hsame :
      (primeOrbitRepresentative hp hpb C : PrimeOrbitQuotient hp hpb) = x := by
    simpa [C] using primeOrbitRepresentative_quotient hp hpb C
  obtain ⟨j, hj, hrep⟩ :=
    (same_primeBaseOrbit_iff hp hpb
      (primeOrbitRepresentative hp hpb C) x).mp hsame
  exact ⟨(C, ⟨j, hj⟩), hrep⟩

/-- The concrete coset ordering has no duplication. -/
theorem primeCosetOrdering_injective {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    Function.Injective (primeCosetOrdering hp hpb) := by
  rintro ⟨C, r⟩ ⟨D, s⟩ h
  have hC : C = D := by
    calc
      C = (primeCosetOrdering hp hpb (C, r) : PrimeOrbitQuotient hp hpb) :=
        (primeCosetOrdering_quotient hp hpb C r).symm
      _ = (primeCosetOrdering hp hpb (D, s) : PrimeOrbitQuotient hp hpb) :=
        congrArg (fun x : (ZMod p)ˣ =>
          (x : PrimeOrbitQuotient hp hpb)) h
      _ = D := primeCosetOrdering_quotient hp hpb D s
  subst D
  have hpow : (primeBaseUnit b p hp hpb) ^ r.val =
      (primeBaseUnit b p hp hpb) ^ s.val := by
    apply mul_left_cancel (a := primeOrbitRepresentative hp hpb C)
    exact h
  have hrs : r.val = s.val := pow_injOn_Iio_orderOf
    r.isLt s.isLt hpow
  rw [Fin.ext hrs]

/-- Exact equivalence implementing the manuscript's multiplicative-coset
ordering. -/
noncomputable def primeCosetOrderingEquiv {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    PrimeOrbitQuotient hp hpb × Fin (primeBasePeriod b p hp hpb) ≃
      (ZMod p)ˣ :=
  Equiv.ofBijective (primeCosetOrdering hp hpb)
    ⟨primeCosetOrdering_injective hp hpb,
      primeCosetOrdering_surjective hp hpb⟩

@[simp] theorem primeCosetOrderingEquiv_apply {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (x : PrimeOrbitQuotient hp hpb × Fin (primeBasePeriod b p hp hpb)) :
    primeCosetOrderingEquiv hp hpb x = primeCosetOrdering hp hpb x := by
  simp [primeCosetOrderingEquiv]

/-- Advancing an ordered phase by `s` shifts the emitted long-division word
by exactly `s` positions. -/
theorem primeCosetOrdering_digit_shift {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb)
    (r : Fin (primeBasePeriod b p hp hpb)) (j : ℕ) :
    primeOrbitDigit hp hpb (primeCosetOrdering hp hpb (C, r)) j =
      primeOrbitDigit hp hpb (primeOrbitRepresentative hp hpb C)
        (j + r.val) := by
  exact primeOrbitDigit_mul_base_pow hp hpb
    (primeOrbitRepresentative hp hpb C) j r.val

/-! ## Nonzero natural residues and unit residues -/

/-- A positive proper prime residue as a unit modulo the prime. -/
noncomputable def primeResidueToUnit {p : ℕ} (hp : p.Prime) :
    PrimeResidue p → (ZMod p)ˣ :=
  fun r => ZMod.unitOfCoprime r.val
    ((hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt r.property.1 r.property.2)).symm)

/-- A unit modulo a prime as its unique positive natural representative. -/
noncomputable def unitToPrimeResidue {p : ℕ} (hp : p.Prime) :
    (ZMod p)ˣ → PrimeResidue p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro x
  exact ⟨(x : ZMod p).val,
    ZMod.val_pos.mpr (Units.ne_zero x), ZMod.val_lt _⟩

/-- Exact equivalence between the manuscript's natural residue indices and
the multiplicative unit group. -/
noncomputable def primeResidueUnitEquiv {p : ℕ} (hp : p.Prime) :
    PrimeResidue p ≃ (ZMod p)ˣ where
  toFun := primeResidueToUnit hp
  invFun := unitToPrimeResidue hp
  left_inv := by
    intro r
    apply Subtype.ext
    simp [primeResidueToUnit, unitToPrimeResidue,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt r.property.2]
  right_inv := by
    intro x
    apply Units.ext
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    simp [primeResidueToUnit, unitToPrimeResidue,
      ZMod.coe_unitOfCoprime]

@[simp] theorem primeResidueUnitEquiv_apply_val {p : ℕ} (hp : p.Prime)
    (r : PrimeResidue p) :
    ((primeResidueUnitEquiv hp r : (ZMod p)ˣ) : ZMod p).val = r.val := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  simp [primeResidueUnitEquiv, primeResidueToUnit,
    ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt r.property.2]

/-- The unit-orbit digit is exactly the manuscript's ordinary long-division
digit started at the corresponding natural residue. -/
theorem primeOrbitDigit_eq_digitAt_unit_val {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (x : (ZMod p)ˣ) (j : ℕ) :
    primeOrbitDigit hp hpb x j = digitAt b p ((x : ZMod p).val) j := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  unfold primeOrbitDigit digitAt
  congr 1
  have heq :
      ((((primeBaseUnit b p hp hpb) ^ j * x : (ZMod p)ˣ) : ZMod p)) =
        ((b ^ j * (x : ZMod p).val : ℕ) : ZMod p) := by
    simp [primeBaseUnit, ZMod.coe_unitOfCoprime]
  calc
    (((((primeBaseUnit b p hp hpb) ^ j * x : (ZMod p)ˣ) : ZMod p))).val =
        ((b ^ j * (x : ZMod p).val : ℕ) : ZMod p).val :=
      congrArg ZMod.val heq
    _ = (b ^ j * (x : ZMod p).val) % p :=
      ZMod.val_natCast p _

/-- Specialization to the natural-residue equivalence. -/
theorem primeOrbitDigit_primeResidue {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (r : PrimeResidue p) (j : ℕ) :
    primeOrbitDigit hp hpb (primeResidueUnitEquiv hp r) j =
      digitAt b p r.val j := by
  rw [primeOrbitDigit_eq_digitAt_unit_val,
    primeResidueUnitEquiv_apply_val]

/-- Emitted digits depend only on the exponent modulo the multiplicative
period. -/
theorem primeOrbitDigit_mod_period {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (x : (ZMod p)ˣ) (j : ℕ) :
    primeOrbitDigit hp hpb x (j % primeBasePeriod b p hp hpb) =
      primeOrbitDigit hp hpb x j := by
  unfold primeOrbitDigit
  congr 1
  have hpow := pow_mod_orderOf (primeBaseUnit b p hp hpb) j
  have hperiod : orderOf (primeBaseUnit b p hp hpb) =
      primeBasePeriod b p hp hpb := by
    simp [primeBaseUnit, primeBasePeriod]
  rw [hperiod] at hpow
  rw [hpow]

end NField.Alignment.PrimeCosetOrdering
