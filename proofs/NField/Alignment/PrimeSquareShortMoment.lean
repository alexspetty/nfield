/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarrySpectralBridge
import NField.Alignment.PrimitiveOddBoundaryMean

/-! # Short-window orthogonality at a prime square

The four general orthogonality lemmas are moved below the paper layer from
PrimeSquareMagnitudeShortMoment. Their proofs are reused without changing the
character family, zero extension or primitive gate.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimeSquareShortMoment
open scoped BigOperators ComplexConjugate ZMod
open CollisionCharacterStructure PrimeSquareCollisionWindow PrimeSquareBoundaryFlux
  PrimitiveOddBoundaryMean PrimeCarrySpectralBridge
attribute [local instance] Classical.propDecidable

theorem firstWindowUnit_neg_ne {b : ℕ} (hb : b.Prime)
    (i j : FirstWindowIndex b) : -(firstWindowUnit hb i) ≠ firstWindowUnit hb j := by
  letI : NeZero (b ^ 2) := ⟨pow_ne_zero 2 hb.ne_zero⟩
  letI : Fact (1 < b ^ 2) := ⟨by nlinarith [hb.two_le]⟩
  intro he
  have hv := congrArg (fun u : UnitClass (b ^ 2) => u.val.val) he
  have hn : (firstWindowUnit hb i).val ≠ 0 := Units.ne_zero _
  rw [Units.val_neg, ZMod.neg_val, if_neg hn,
    firstWindowUnit_val hb i, firstWindowUnit_val hb j] at hv
  have hi := firstWindowNat_lt hb.two_le i
  have hj := firstWindowNat_lt hb.two_le j
  have hb2 := hb.two_le
  have hi2 : firstWindowNat i ≤ b ^ 2 := by nlinarith
  have hsum : firstWindowNat i + firstWindowNat j = b ^ 2 := by omega
  nlinarith

theorem odd_packet_second_moment {m : ℕ} [NeZero m]
    {ι : Type*} [Fintype ι] (x : ι → UnitClass m) :
    (∑ χ : Character m with χ.Odd,
      (Complex.normSq (∑ i, χ (x i).val) : ℂ)) =
      ∑ i, ∑ j, oddCharacterKernel (x i) (x j) := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold oddCharacterKernel
  apply Finset.sum_congr rfl
  intro χ _
  simp only [starRingEnd_apply]
  ring

theorem odd_shortWindow_second_moment {b : ℕ} (hb : b.Prime) :
    (∑ χ : Character (b ^ 2) with χ.Odd,
      (Complex.normSq (shortWindowSum hb χ) : ℂ)) =
      (1 / 2 : ℂ) * ((b ^ 2).totient : ℂ) * (b - 1 : ℕ) := by
  classical
  letI : NeZero (b ^ 2) := ⟨pow_ne_zero 2 hb.ne_zero⟩
  unfold shortWindowSum
  rw [odd_packet_second_moment]
  simp_rw [oddCharacterKernel_eq, if_neg (firstWindowUnit_neg_ne hb _ _)]
  simp_rw [sub_zero, (firstWindowUnit_injective hb).eq_iff]
  simp
  ring

theorem primitive_odd_shortWindow_second_moment {b : ℕ}
    [NeZero b] [NeZero (b ^ 2)] (hb : b.Prime) :
    (∑ χ : Character (b ^ 2) with χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (shortWindowSum hb χ) : ℂ)) =
      (1 / 2 : ℂ) * ((b ^ 2).totient : ℂ) * (b - 1 : ℕ) := by
  classical
  rw [← odd_shortWindow_second_moment hb]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hodd : χ.Odd
  · by_cases hprim : χ.IsPrimitive
    · simp [hodd, hprim]
    · rw [shortWindowSum_eq_zero_of_imprimitive_odd hb χ hprim hodd]
      simp
  · simp [hodd]

end NField.Alignment.PrimeSquareShortMoment
