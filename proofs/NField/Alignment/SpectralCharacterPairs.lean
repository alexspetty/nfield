/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareCharacterPairs
import NField.Alignment.FiniteConjugatePairing

/-! # The actual primitive odd character pairs -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SpectralCharacterPairs
open scoped BigOperators
open CollisionCharacterStructure PrimitiveOddBoundaryMean
open FiniteConjugatePairing

/-- The same literal subtype used by the magnitude family, without importing
its later reader-facing papers into this earlier title. -/
abbrev PrimitiveOddFamily (b : ℕ) :=
  {χ : Character (b ^ 2) // χ.IsPrimitive ∧ χ.Odd}

instance primitiveFamilyFintype (b : ℕ) : Fintype (PrimitiveOddFamily b) := Fintype.ofFinite _

abbrev OddFamily (b : ℕ) := {χ : Character (b ^ 2) // χ.Odd}

instance oddFamilyFintype (b : ℕ) : Fintype (OddFamily b) := Fintype.ofFinite _

def conjugate {b : ℕ} (χ : PrimitiveOddFamily b) : PrimitiveOddFamily b :=
  ⟨star χ.val, by
    constructor
    · simpa [MulChar.star_eq_inv] using CarryBoundarySpectra.inverse_isPrimitive χ.property.1
    · change (star χ.val) (-1) = -1
      rw [MulChar.star_apply, χ.property.2]
      simp⟩

theorem conjugate_involutive (b : ℕ) : Function.Involutive (@conjugate b) := by
  intro χ
  exact Subtype.ext (star_star χ.val)

theorem conjugate_ne {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (χ : PrimitiveOddFamily b) : conjugate χ ≠ χ := by
  intro h
  exact PrimeSquareCharacterPairs.primitive_ne_conjugate hb hbodd χ.val χ.property.1
    (congrArg Subtype.val h)

abbrev Pairs (b : ℕ) := Representatives (@conjugate b)

theorem primitive_population {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (Fintype.card (PrimitiveOddFamily b) : ℝ) = (((b - 1) ^ 2 : ℕ) : ℝ) / 2 := by
  classical
  have hcard : Fintype.card (PrimitiveOddFamily b) = primitiveOddCharacterCount (b ^ 2) := by
    simp [PrimitiveOddFamily, primitiveOddCharacterCount, Fintype.card_subtype]
  rw [hcard, primitiveOddCharacterCount_primePower_real hb hbodd (by decide : 2 ≤ 2)]
  rw [Nat.totient_prime_pow hb (by decide : 0 < 2),
    Nat.totient_prime_pow hb (by decide : 0 < 2 - 1)]
  simp only [Nat.reduceSub, pow_one, pow_zero, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hb.one_le, Nat.cast_one]
  ring

theorem family_nonempty {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) : Nonempty (PrimitiveOddFamily b) := by
  have hb1 : 0 < b - 1 := by have := hb.one_lt; omega
  have hc : 0 < (Fintype.card (PrimitiveOddFamily b) : ℝ) := by
    rw [primitive_population hb hbodd]
    positivity
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hc)

theorem odd_population {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (Fintype.card (OddFamily b) : ℝ) = (b : ℝ) * (b - 1 : ℝ) / 2 := by
  classical
  have hb2 : 2 < b := by have := hb.two_le; omega
  letI : Fact (2 < b ^ 2) := ⟨by nlinarith⟩
  have hneg : (- (1 : UnitClass (b ^ 2))) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)
  have hkernel := oddCharacterKernel_eq (1 : UnitClass (b ^ 2)) 1
  have hc : (Fintype.card (OddFamily b) : ℂ) =
      ((b ^ 2).totient : ℂ) / 2 := by
    simpa [oddCharacterKernel, OddFamily, Fintype.card_subtype, hneg,
      Nat.cast_mul, div_eq_mul_inv, mul_comm] using hkernel
  have hr := congrArg Complex.re hc
  norm_num at hr
  rw [hr, Nat.totient_prime_pow hb (by decide : 0 < 2)]
  simp only [Nat.reduceSub, pow_one, Nat.cast_mul, Nat.cast_sub hb.one_le, Nat.cast_one]

theorem pair_population {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (Fintype.card (Pairs b) : ℝ) = (((b - 1) ^ 2 : ℕ) : ℝ) / 4 := by
  have h := twice_pair_count (@conjugate b) (conjugate_involutive b) (conjugate_ne hb hbodd)
  have hr : 2 * (Fintype.card (Pairs b) : ℝ) =
      (Fintype.card (PrimitiveOddFamily b) : ℝ) := by exact_mod_cast h
  rw [primitive_population hb hbodd] at hr
  linarith

theorem base_three_one_pair : Fintype.card (Pairs 3) = 1 := by
  have h := pair_population (b := 3) (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

theorem pair_mass_sum {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (w : PrimitiveOddFamily b → ℝ)
    (hw : ∑ χ, w χ = 1) : ∑ r : Pairs b, (w r + w (conjugate r)) = 1 :=
  pair_masses_sum _ (conjugate_involutive b) (conjugate_ne hb hbodd) w hw

theorem pair_overlap {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (w v : PrimitiveOddFamily b → ℝ)
    (hw : ∀ χ, w (conjugate χ) = w χ) (hv : ∀ χ, v (conjugate χ) = v χ) :
    (Fintype.card (PrimitiveOddFamily b) : ℝ) * ∑ χ, w χ * v χ =
      (Fintype.card (Pairs b) : ℝ) *
        ∑ r : Pairs b, (w r + w (conjugate r)) * (v r + v (conjugate r)) :=
  scaled_overlap_pairs _ (conjugate_involutive b) (conjugate_ne hb hbodd) w v hw hv

end NField.Alignment.SpectralCharacterPairs
