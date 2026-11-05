/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectrumLandscape
import NField.Alignment.CollisionRamanujan

/-! # Literal Laurent and Ramanujan identities in the base-five ledger -/

noncomputable section
namespace NField.Alignment.BaseFiveLaurentLedger
open CollisionSpectrumLandscape CollisionRamanujan

def shortLaurent (z : ℂ) : ℂ :=
  baseFiveShortPolynomial z * baseFiveShortPolynomial z⁻¹

def cyclicEvenSquare (z : ℂ) : ℂ :=
  32 + 14 * (z ^ 2 + z⁻¹ ^ 2) + 7 * (z ^ 4 + z⁻¹ ^ 4) +
    17 * (z ^ 6 + z⁻¹ ^ 6) + 9 * (z ^ 8 + z⁻¹ ^ 8) + 2 * z ^ 10

theorem short_laurent_expansion (z : ℂ) (hz : z ≠ 0) :
    shortLaurent z = 4 + 2 * (z + z⁻¹) + (z ^ 2 + z⁻¹ ^ 2) +
      (z ^ 5 + z⁻¹ ^ 5) + (z ^ 6 + z⁻¹ ^ 6) + (z ^ 7 + z⁻¹ ^ 7) := by
  unfold shortLaurent baseFiveShortPolynomial
  field_simp
  ring

theorem even_square_certificate (z : ℂ) (hz : z ≠ 0) :
    z ^ 14 * ((shortLaurent z ^ 2 + shortLaurent (-z) ^ 2) / 2 -
      cyclicEvenSquare z) =
      (z ^ 20 - 1) * (z ^ 8 + 3 * z ^ 6 - z ^ 4 - 3 * z ^ 2 - 1) := by
  unfold shortLaurent baseFiveShortPolynomial cyclicEvenSquare
  field_simp
  ring

theorem even_square_mod_twenty (z : ℂ) (hz : z ≠ 0) (h20 : z ^ 20 = 1) :
    (shortLaurent z ^ 2 + shortLaurent (-z) ^ 2) / 2 = cyclicEvenSquare z := by
  have h := even_square_certificate z hz
  rw [h20, sub_self, zero_mul] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 14 hz))

theorem ramanujan_twenty_formula (n : ℤ) :
    ramanujan 20 n =
      (if (2 : ℤ) ∣ n then 2 else 0) - (if (4 : ℤ) ∣ n then 4 else 0) -
      (if (10 : ℤ) ∣ n then 10 else 0) + (if (20 : ℤ) ∣ n then 20 else 0) := by
  have hd : Nat.divisors 20 = {1, 2, 4, 5, 10, 20} := by decide
  have hm : ArithmeticFunction.moebius 20 = 0 ∧ ArithmeticFunction.moebius 10 = 1 ∧
      ArithmeticFunction.moebius 5 = -1 ∧ ArithmeticFunction.moebius 4 = 0 ∧
      ArithmeticFunction.moebius 2 = -1 ∧ ArithmeticFunction.moebius 1 = 1 := by
    refine ⟨ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide), ?_,
      ArithmeticFunction.moebius_apply_prime (by decide),
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide),
      ArithmeticFunction.moebius_apply_prime (by decide),
      ArithmeticFunction.moebius_apply_one⟩
    change ArithmeticFunction.moebius (2 * 5) = 1
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)]
    norm_num
  simp only [ramanujan, hd]
  norm_num [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2]
  split_ifs <;> norm_num

theorem actual_ramanujan_twenty_values :
    primitiveSum 20 0 = 8 ∧ primitiveSum 20 2 = 2 ∧
      primitiveSum 20 4 = -2 ∧ primitiveSum 20 6 = 2 ∧
      primitiveSum 20 8 = -2 ∧ primitiveSum 20 10 = -8 := by
  norm_num [primitiveSum_eq_ramanujan, ramanujan_twenty_formula]

theorem actual_ramanujan_twenty_odd_zero (n : ℤ) (hn : ¬ (2 : ℤ) ∣ n) :
    primitiveSum 20 n = 0 := by
  have h4 : ¬ (4 : ℤ) ∣ n := fun h => hn (dvd_trans (by norm_num) h)
  have h10 : ¬ (10 : ℤ) ∣ n := fun h => hn (dvd_trans (by norm_num) h)
  have h20 : ¬ (20 : ℤ) ∣ n := fun h => hn (dvd_trans (by norm_num) h)
  simp [primitiveSum_eq_ramanujan, ramanujan_twenty_formula, hn, h4, h10, h20]

end NField.Alignment.BaseFiveLaurentLedger
