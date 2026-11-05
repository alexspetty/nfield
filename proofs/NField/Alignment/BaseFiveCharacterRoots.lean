/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFiveCharacterPolynomial
import NField.Alignment.SpectralCharacterPairs
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Actual base-five characters and the eight primitive exponents -/

noncomputable section
namespace NField.Alignment.BaseFiveCharacterRoots
open CollisionCharacterStructure BaseFiveCharacterPolynomial CollisionSpectrumLandscape
  SpectralCharacterPairs

def generator : UnitClass 25 := ZMod.unitOfCoprime 2 (by decide)

theorem generator_order : orderOf generator = 20 := by
  apply (orderOf_eq_iff (by decide : 0 < 20)).2
  constructor
  · apply Units.ext
    decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem generator_pow_injective : Function.Injective (fun j : Fin 20 => generator ^ j.val) := by
  intro i j hij
  apply Fin.ext
  have h : IsPrimitiveRoot generator 20 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact generator_order
  exact h.pow_inj i.isLt j.isLt hij

def generatorEquiv : Fin 20 ≃ UnitClass 25 :=
  Equiv.ofBijective (fun j => generator ^ j.val)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨generator_pow_injective, by rw [Fintype.card_fin, ZMod.card_units_eq_totient]; decide⟩)

theorem character_value_isPrimitiveRoot (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) : IsPrimitiveRoot (χ 2) 20 := by
  have ht := odd_character_two_tenth χ hodd
  have h20 : χ 2 ^ 20 = 1 := by
    calc
      χ 2 ^ 20 = (χ 2 ^ 10) ^ 2 := by ring
      _ = 1 := by rw [ht]; norm_num
  have hd : orderOf (χ 2) ∈ Nat.divisors 20 :=
    Nat.mem_divisors.mpr ⟨orderOf_dvd_of_pow_eq_one h20, by decide⟩
  have hnot : ¬ orderOf (χ 2) ∣ 10 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [ht]
    norm_num
  have h4 : orderOf (χ 2) ≠ 4 := by
    intro he
    have hp4 : χ 2 ^ 4 = 1 := by simpa only [he] using pow_orderOf_eq_one (χ 2)
    have hp2 : χ 2 ^ 2 = -1 := by
      calc
        χ 2 ^ 2 = (χ 2 ^ 4) ^ 2 * χ 2 ^ 2 := by rw [hp4]; ring
        _ = χ 2 ^ 10 := by ring
        _ = -1 := ht
    have hr := primitive_odd_cyclotomic_twenty χ hprim hodd
    have h6 : χ 2 ^ 6 = -1 := by
      calc
        χ 2 ^ 6 = χ 2 ^ 4 * χ 2 ^ 2 := by ring
        _ = -1 := by rw [hp4, hp2]; norm_num
    have h8 : χ 2 ^ 8 = 1 := by
      calc
        χ 2 ^ 8 = (χ 2 ^ 4) ^ 2 := by ring
        _ = 1 := by rw [hp4]; norm_num
    norm_num [cyclotomicTwentyValue, hp2, hp4, h6, h8] at hr
  rw [show Nat.divisors 20 = {1, 2, 4, 5, 10, 20} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h | h | h
  · simp [h] at hnot
  · norm_num [h] at hnot
  · exact (h4 h).elim
  · norm_num [h] at hnot
  · simp [h] at hnot
  · rwa [IsPrimitiveRoot.iff_orderOf]

theorem character_generator_injective :
    Function.Injective (fun χ : Character 25 => χ (2 : ZMod 25)) := by
  intro χ ψ he
  change χ (2 : ZMod 25) = ψ (2 : ZMod 25) at he
  apply MulChar.ext
  intro u
  obtain ⟨j, hj⟩ := generatorEquiv.surjective u
  change generator ^ j.val = u at hj
  rw [← hj, Units.val_pow_eq_pow_val, map_pow, map_pow]
  change χ (2 : ZMod 25) ^ j.val = ψ (2 : ZMod 25) ^ j.val
  rw [he]

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

theorem zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 20 :=
  Complex.isPrimitiveRoot_exp 20 (by decide)

abbrev PrimitiveExponent := {j : Fin 20 // j.val.Coprime 20}

theorem primitive_exponent_card : Fintype.card PrimitiveExponent = 8 := by decide

theorem character_exponent_exists (χ : PrimitiveOddFamily 5) :
    ∃ j : PrimitiveExponent, zeta ^ j.val.val = χ.val 2 := by
  obtain ⟨j, hj, hc, he⟩ := zeta_isPrimitiveRoot.isPrimitiveRoot_iff.mp
    (character_value_isPrimitiveRoot χ.val χ.property.1 χ.property.2)
  exact ⟨⟨⟨j, hj⟩, hc⟩, he⟩

def characterExponent (χ : PrimitiveOddFamily 5) : PrimitiveExponent :=
  Classical.choose (character_exponent_exists χ)

theorem characterExponent_spec (χ : PrimitiveOddFamily 5) :
    zeta ^ (characterExponent χ).val.val = χ.val 2 :=
  Classical.choose_spec (character_exponent_exists χ)

theorem characterExponent_bijective : Function.Bijective characterExponent := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro χ ψ he
    apply Subtype.ext
    apply character_generator_injective
    change χ.val 2 = ψ.val 2
    rw [← characterExponent_spec, ← characterExponent_spec, he]
  · rw [primitive_exponent_card]
    have h := primitive_population (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
    norm_num at h
    exact_mod_cast h

def characterExponentEquiv : PrimitiveOddFamily 5 ≃ PrimitiveExponent :=
  Equiv.ofBijective characterExponent characterExponent_bijective

end NField.Alignment.BaseFiveCharacterRoots
