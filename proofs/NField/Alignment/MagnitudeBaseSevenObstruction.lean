/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeBaseSevenCharacter
import NField.Alignment.MagnitudeDiagonalReduction

/-!
# No common diagonal/Bernoulli magnitude ratio at base seven

This is the whole statement of Proposition 4 for the actual complete
primitive odd family. The moments determine the only possible squared
ratio. The explicitly constructed character contradicts it by the proved
cyclotomic certificate.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeBaseSeven

open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.SpectralRepulsion

theorem base_seven_square_ratio :
    uniformAverage (fun χ : PrimitiveOddFamily 7 => ‖diagonalSum 7 χ‖^2) /
      uniformAverage (fun χ : PrimitiveOddFamily 7 => ‖bernoulliSum 7 χ‖^2) =
      (28/8 : ℝ) := by
  rw [diagonalSum_square_average (by decide : Nat.Prime 7) (by decide),
    bernoulli_magnitude_second_moment (by decide : Nat.Prime 7) (by decide)]
  norm_num

/-- Whole Proposition 4, with no assumed character or polynomial certificate. -/
theorem base_seven_nonproportionality :
    ¬ ∃ c : ℝ, ∀ χ : PrimitiveOddFamily 7,
      ‖diagonalSum 7 χ‖ = c * ‖bernoulliSum 7 χ‖ := by
  rintro ⟨c, hc⟩
  have hratio := baseSeven_proportionality_forces_square hc
  let z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 14)
  have hz : IsPrimitiveRoot z 14 := Complex.isPrimitiveRoot_exp 14 (by decide)
  have hw := hc (witness z hz)
  rw [diagonalSum_norm (by decide : Nat.Prime 7)] at hw
  have hs := congrArg (fun t : ℝ => t^2) hw
  simp only [mul_pow] at hs
  rw [hratio] at hs
  apply witness_square_discrepancy hz
  simp only [Complex.normSq_eq_norm_sq]
  nlinarith

end NField.Alignment.MagnitudeBaseSeven
