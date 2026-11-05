/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFiveCharacterPolynomial
import NField.Alignment.BaseFiveCharacterRoots

/-! # The printed residue lists and paired Bernoulli polynomial -/

noncomputable section
namespace NField.Alignment.BaseFiveArithmeticDetails
open scoped BigOperators
open CollisionCharacterStructure CollisionSpectrumLandscape BaseFiveCharacterPolynomial
  CarryBoundarySpectra

theorem residue_power_list :
    List.ofFn (fun r : Fin 10 => (2 ^ r.val) % 25) =
      [1, 2, 4, 8, 16, 7, 14, 3, 6, 12] := by decide

theorem primitive_exponent_list :
    (Finset.range 20).filter (fun j => j.Coprime 20) = {1, 3, 7, 9, 11, 13, 17, 19} := by
  decide

theorem paired_residue_powers (r : Fin 10) :
    (2 ^ (r.val + 10)) % 25 = 25 - (2 ^ r.val) % 25 := by
  revert r
  decide +kernel

theorem paired_character_powers (χ : Character 25) (hodd : χ.Odd) (r : ℕ) :
    χ 2 ^ (r + 10) = -(χ 2 ^ r) := by
  rw [pow_add, odd_character_two_tenth χ hodd]
  ring

theorem paired_bernoulli_polynomial (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    25 * bernoulliOne χ =
      ∑ r : Fin 10, (2 * (((2 ^ r.val) % 25 : ℕ) : ℂ) - 25) * χ 2 ^ r.val := by
  rw [bernoulli_character_polynomial χ hprim hodd]
  norm_num [Fin.sum_univ_succ, baseFiveBernoulliPolynomial]
  have h := primitive_odd_cyclotomic_twenty χ hprim hodd
  unfold cyclotomicTwentyValue at h
  linear_combination (13 + χ 2) * h

end NField.Alignment.BaseFiveArithmeticDetails
