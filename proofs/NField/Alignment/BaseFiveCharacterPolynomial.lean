/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveReductionFiber
import NField.Alignment.LandscapeActualSpectrum

/-! # Actual primitive characters in the base-five polynomial certificate -/

noncomputable section
namespace NField.Alignment.BaseFiveCharacterPolynomial
open scoped BigOperators ComplexConjugate
open CollisionCharacterStructure CenteredCollisionSum CollisionTransform
  NeutralityTheorem PrimeCarryFiberCentering PrimitiveReductionFiber CollisionSpectrumLandscape

theorem primitive_kernel_five_sum (χ : Character 25) (hχ : χ.IsPrimitive) :
    1 + χ 6 + χ 11 + χ 16 + χ 21 = 0 := by
  letI : NeZero (allLagModulus 5 1) := ⟨by decide⟩
  have hs := primitive_fiber_sum_zero (N := 25) (d := 5)
    (by decide) (by decide) χ hχ (1 : UnitClass 5)
  have hf : (∑ a : Fiber (coarseUnitReduction 5 1) (1 : UnitClass 5), χ a.val.val) = 0 := by
    exact hs
  have he := Equiv.sum_comp (primeFiberEquiv (by decide : Nat.Prime 5) (1 : UnitClass 5))
    (fun a => χ a.val.val)
  have hsum : (∑ i : Fin 5,
      χ (primeFiberCoordinate (by decide : Nat.Prime 5) (1 : UnitClass 5) i).val) = 0 :=
    he.trans hf
  norm_num [primeFiberCoordinate, Fin.sum_univ_succ] at hsum
  have hcast : (ZMod.cast (1 : ZMod 5) : ZMod (allLagModulus 5 1)) = 1 := by
    decide
  rw [hcast] at hsum
  change χ (1 : ZMod 25) + (χ 6 + (χ 11 + (χ 16 + χ 21))) = 0 at hsum
  rw [map_one] at hsum
  linear_combination hsum

theorem odd_character_two_tenth (χ : Character 25) (hodd : χ.Odd) :
    χ 2 ^ 10 = -1 := by
  rw [← map_pow, show (2 : ZMod 25) ^ 10 = -1 by decide]
  exact hodd

/-- Primitivity supplies the missing cyclotomic hypothesis for the actual
character value at the generator. -/
theorem primitive_odd_cyclotomic_twenty (χ : Character 25)
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) : cyclotomicTwentyValue (χ 2) = 0 := by
  have h := primitive_kernel_five_sum χ hχ
  have hten := odd_character_two_tenth χ hodd
  have h6 : χ 6 = χ 2 ^ 8 := by rw [← map_pow]; congr 1
  have h11 : χ 11 = χ 2 ^ 16 := by rw [← map_pow]; congr 1
  have h16 : χ 16 = χ 2 ^ 4 := by rw [← map_pow]; congr 1
  have h21 : χ 21 = χ 2 ^ 12 := by rw [← map_pow]; congr 1
  rw [h6, h11, h16, h21] at h
  have htwelve : χ 2 ^ 12 = -(χ 2 ^ 2) := by
    calc
      χ 2 ^ 12 = χ 2 ^ 10 * χ 2 ^ 2 := by ring
      _ = -(χ 2 ^ 2) := by rw [hten]; ring
  have hsixteen : χ 2 ^ 16 = -(χ 2 ^ 6) := by
    calc
      χ 2 ^ 16 = χ 2 ^ 10 * χ 2 ^ 6 := by ring
      _ = -(χ 2 ^ 6) := by rw [hten]; ring
  rw [htwelve, hsixteen] at h
  unfold cyclotomicTwentyValue
  linear_combination h


/-- The short sum is the actual character polynomial at the generator. -/
theorem short_character_polynomial (χ : Character 25) :
    (∑ k ∈ Finset.Icc (1 : ℕ) 4, χ (k : ZMod 25)) = baseFiveShortPolynomial (χ 2) := by
  have h3 : χ 3 = χ 2 ^ 7 := by rw [← map_pow]; congr 1
  have h4 : χ 4 = χ 2 ^ 2 := by rw [← map_pow]; congr 1
  norm_num [Finset.sum_Icc_succ_top, baseFiveShortPolynomial, h3, h4]
  ring

/-- Exact Bernoulli normalization for every actual primitive odd character. -/
theorem bernoulli_character_polynomial (χ : Character 25)
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    CarryBoundarySpectra.bernoulliOne χ =
      -(2 / 5 : ℂ) * baseFiveBernoulliPolynomial (χ 2) := by
  have hroot := primitive_odd_cyclotomic_twenty χ hχ hodd
  have hten := odd_character_two_tenth χ hodd
  have hz5 : χ 5 = 0 := by
    apply MulChar.map_nonunit
    decide
  have hz10 : χ 10 = 0 := by
    apply MulChar.map_nonunit
    decide
  have hz15 : χ 15 = 0 := by
    apply MulChar.map_nonunit
    decide
  have hz20 : χ 20 = 0 := by
    apply MulChar.map_nonunit
    decide
  have hc4 : χ 4 = χ 2 ^ 2 := by rw [← map_pow]; congr 1
  have hc8 : χ 8 = χ 2 ^ 3 := by rw [← map_pow]; congr 1
  have hc16 : χ 16 = χ 2 ^ 4 := by rw [← map_pow]; congr 1
  have hc7 : χ 7 = χ 2 ^ 5 := by rw [← map_pow]; congr 1
  have hc14 : χ 14 = χ 2 ^ 6 := by rw [← map_pow]; congr 1
  have hc3 : χ 3 = χ 2 ^ 7 := by rw [← map_pow]; congr 1
  have hc6 : χ 6 = χ 2 ^ 8 := by rw [← map_pow]; congr 1
  have hc12 : χ 12 = χ 2 ^ 9 := by rw [← map_pow]; congr 1
  have hc24 : χ 24 = χ 2 ^ 10 := by rw [← map_pow]; congr 1
  have hc23 : χ 23 = χ 2 ^ 11 := by rw [← map_pow]; congr 1
  have hc21 : χ 21 = χ 2 ^ 12 := by rw [← map_pow]; congr 1
  have hc17 : χ 17 = χ 2 ^ 13 := by rw [← map_pow]; congr 1
  have hc9 : χ 9 = χ 2 ^ 14 := by rw [← map_pow]; congr 1
  have hc18 : χ 18 = χ 2 ^ 15 := by rw [← map_pow]; congr 1
  have hc11 : χ 11 = χ 2 ^ 16 := by rw [← map_pow]; congr 1
  have hc22 : χ 22 = χ 2 ^ 17 := by rw [← map_pow]; congr 1
  have hc19 : χ 19 = χ 2 ^ 18 := by rw [← map_pow]; congr 1
  have hc13 : χ 13 = χ 2 ^ 19 := by rw [← map_pow]; congr 1
  have hsum : (∑ x : ZMod 25, (x.val : ℂ) * χ x) =
      ∑ k ∈ Finset.range 25, (k : ℂ) * χ (k : ZMod 25) := by
    rw [← Fin.sum_univ_eq_sum_range]
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv 25).toEquiv
    intro k
    have he : (ZMod.finEquiv 25).toEquiv k = (k.val : ZMod 25) := by
      simpa using ConductorDepthSawtooth.finEquiv_eq_natCast k
    simp only [he, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  unfold CarryBoundarySpectra.bernoulliOne
  rw [hsum]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, map_one, hz5, hz10, hz15, hz20, hc4, hc8, hc16, hc7, hc14, hc3, hc6, hc12, hc24, hc23, hc21, hc17, hc9, hc18, hc11, hc22, hc19, hc13]
  have hp11 : χ 2 ^ 11 = -(χ 2 ^ 1) := by
    calc
      χ 2 ^ 11 = χ 2 ^ 10 * χ 2 ^ 1 := by ring
      _ = -(χ 2 ^ 1) := by rw [hten]; ring
  have hp12 : χ 2 ^ 12 = -(χ 2 ^ 2) := by
    calc
      χ 2 ^ 12 = χ 2 ^ 10 * χ 2 ^ 2 := by ring
      _ = -(χ 2 ^ 2) := by rw [hten]; ring
  have hp13 : χ 2 ^ 13 = -(χ 2 ^ 3) := by
    calc
      χ 2 ^ 13 = χ 2 ^ 10 * χ 2 ^ 3 := by ring
      _ = -(χ 2 ^ 3) := by rw [hten]; ring
  have hp14 : χ 2 ^ 14 = -(χ 2 ^ 4) := by
    calc
      χ 2 ^ 14 = χ 2 ^ 10 * χ 2 ^ 4 := by ring
      _ = -(χ 2 ^ 4) := by rw [hten]; ring
  have hp15 : χ 2 ^ 15 = -(χ 2 ^ 5) := by
    calc
      χ 2 ^ 15 = χ 2 ^ 10 * χ 2 ^ 5 := by ring
      _ = -(χ 2 ^ 5) := by rw [hten]; ring
  have hp16 : χ 2 ^ 16 = -(χ 2 ^ 6) := by
    calc
      χ 2 ^ 16 = χ 2 ^ 10 * χ 2 ^ 6 := by ring
      _ = -(χ 2 ^ 6) := by rw [hten]; ring
  have hp17 : χ 2 ^ 17 = -(χ 2 ^ 7) := by
    calc
      χ 2 ^ 17 = χ 2 ^ 10 * χ 2 ^ 7 := by ring
      _ = -(χ 2 ^ 7) := by rw [hten]; ring
  have hp18 : χ 2 ^ 18 = -(χ 2 ^ 8) := by
    calc
      χ 2 ^ 18 = χ 2 ^ 10 * χ 2 ^ 8 := by ring
      _ = -(χ 2 ^ 8) := by rw [hten]; ring
  have hp19 : χ 2 ^ 19 = -(χ 2 ^ 9) := by
    calc
      χ 2 ^ 19 = χ 2 ^ 10 * χ 2 ^ 9 := by ring
      _ = -(χ 2 ^ 9) := by rw [hten]; ring
  rw [hten, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19]
  unfold baseFiveBernoulliPolynomial
  unfold cyclotomicTwentyValue at hroot
  linear_combination ((-(13 : ℂ) - χ 2) / 25) * hroot

end NField.Alignment.BaseFiveCharacterPolynomial
