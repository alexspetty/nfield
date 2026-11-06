/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCompletion
import NField.Alignment.DivisorSmallPowerBound

/-! # The sharper two-frequency gcd in complete reciprocal coefficients -/

noncomputable section

namespace NField.Alignment.CommonResetTripleGcd

open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase PrimePowerGcdBound KloostermanCRT
open KloostermanGlobalBound PrimitivePrimePowerBound InverseAdditiveCompletion KloostermanPrimePowerStationary

def jointGcd (q : ℕ) (a b : ZMod q) : ℕ := (a.val.gcd q).gcd (b.val.gcd q)

theorem gcd_pair_modulus (a b q : ℕ) : (a.gcd q).gcd (b.gcd q) = (a.gcd b).gcd q := by
  calc
    _ = (a.gcd b).gcd (q.gcd q) := by ac_rfl
    _ = _ := by rw [Nat.gcd_self]

theorem prime_power_divisors_comparable {p k a b : ℕ} (hp : p.Prime)
    (ha : a ∣ p^k) (hb : b ∣ p^k) : a ∣ b ∨ b ∣ a := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hb
  rcases le_total i j with h | h
  · exact Or.inl (pow_dvd_pow p h)
  · exact Or.inr (pow_dvd_pow p h)

theorem prime_power_joint_bound (p : ℕ) [Fact p.Prime] (k : ℕ) (a b : ZMod (p^k)) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤
      localConstant p*Real.sqrt (p^k : ℕ)*Real.sqrt (jointGcd (p^k) a b : ℝ) := by
  rcases prime_power_divisors_comparable (Fact.out : p.Prime)
    (Nat.gcd_dvd_right a.val (p^k)) (Nat.gcd_dvd_right b.val (p^k)) with h | h
  · rw [jointGcd, Nat.gcd_eq_left h, unitSum_swap]
    exact prime_power_unitSum_gcd_bound p k b a
  · rw [jointGcd, Nat.gcd_eq_right h]
    exact prime_power_unitSum_gcd_bound p k a b

/-- Title: `The complete Kloosterman sum retains the gcd of both actual frequencies and the modulus`. -/
theorem unitSum_joint_divisor_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤
      divisorCost q*Real.sqrt (q : ℝ)*Real.sqrt (jointGcd q a b : ℝ) := by
  have hall : ∀ q, ∀ [NeZero q], ∀ a b : ZMod q,
      ‖unitSum ZMod.stdAddChar a b‖ ≤
        divisorCost q*Real.sqrt (q : ℝ)*Real.sqrt (jointGcd q a b : ℝ) := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p k hp hk inst a b
      letI : Fact p.Prime := ⟨hp⟩
      exact (prime_power_joint_bound p k a b).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (localConstant_le_divisorCost p k hk)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    · intro inst
      exact (NeZero.ne (0 : ℕ) rfl).elim
    · intro inst a b
      have ha : a=0 := Subsingleton.elim _ _
      have hb : b=0 := Subsingleton.elim _ _
      subst a b
      simp [unitSum, phase, divisorCost, exceptionalFactor, jointGcd]
    · intro m n hm hn h ih_m ih_n inst a b
      letI : NeZero m := ⟨by omega⟩
      letI : NeZero n := ⟨by omega⟩
      rw [norm_unitSum_crt m n h]
      have hmB := ih_m (leftTwist m n*leftReduction m n a) (leftTwist m n*leftReduction m n b)
      have hnB := ih_n (rightTwist m n*rightReduction m n a) (rightTwist m n*rightReduction m n b)
      simp only [jointGcd, left_twist_gcd m n h, right_twist_gcd m n h] at hmB hnB
      change _ ≤ divisorCost m*Real.sqrt (m : ℝ)*
        Real.sqrt (Nat.gcd
          (Nat.gcd (ZMod.castHom (dvd_mul_right m n) (ZMod m) a).val m)
          (Nat.gcd (ZMod.castHom (dvd_mul_right m n) (ZMod m) b).val m) : ℝ) at hmB
      change _ ≤ divisorCost n*Real.sqrt (n : ℝ)*
        Real.sqrt (Nat.gcd
          (Nat.gcd (ZMod.castHom (dvd_mul_left n m) (ZMod n) a).val n)
          (Nat.gcd (ZMod.castHom (dvd_mul_left n m) (ZMod n) b).val n) : ℝ) at hnB
      rw [gcd_reduction, gcd_reduction, gcd_pair_modulus] at hmB hnB
      calc
        _ ≤ (divisorCost m*Real.sqrt (m : ℝ)*Real.sqrt ((a.val.gcd b.val).gcd m : ℝ))*
            (divisorCost n*Real.sqrt (n : ℝ)*Real.sqrt ((a.val.gcd b.val).gcd n : ℝ)) :=
          mul_le_mul hmB hnB (norm_nonneg _)
            (mul_nonneg (mul_nonneg (divisorCost_nonneg m) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _))
        _ = _ := by
          rw [jointGcd, gcd_pair_modulus, divisorCost_mul m n h,
            Nat.Coprime.gcd_mul (a.val.gcd b.val) h, Nat.cast_mul, Nat.cast_mul,
            Real.sqrt_mul (Nat.cast_nonneg m),
            Real.sqrt_mul (Nat.cast_nonneg ((a.val.gcd b.val).gcd m))]
          ring
  exact hall q a b

theorem unitSum_joint_uniform_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤
      4*Real.sqrt (q : ℝ)*q.divisors.card*Real.sqrt (jointGcd q a b : ℝ) := by
  have hc : divisorCost q ≤ 4*q.divisors.card :=
    mul_le_mul_of_nonneg_right (exceptionalFactor_bounds q).2 (Nat.cast_nonneg _)
  calc
    _ ≤ divisorCost q*Real.sqrt (q : ℝ)*Real.sqrt (jointGcd q a b : ℝ) :=
      unitSum_joint_divisor_bound q a b
    _ ≤ (4*q.divisors.card)*Real.sqrt (q : ℝ)*Real.sqrt (jointGcd q a b : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Title: `The normalized reciprocal Fourier coefficient has the sharper three-argument gcd bound`. -/
theorem reciprocal_coefficient_joint_bound {q : ℕ} [NeZero q] (n h : ZMod q) :
    ‖(q : ℂ)⁻¹*ZMod.dft (inversePhase 1 n) h‖ ≤
      (4*Real.sqrt (q : ℝ)*q.divisors.card*Real.sqrt (jointGcd q (-h) n : ℝ))/(q : ℝ) := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, inverse_phase_dft,
    complete_inverse_eq_unitSum]
  simp only [Nat.cast_one, mul_one]
  calc
    _ ≤ (q : ℝ)⁻¹*(4*Real.sqrt (q : ℝ)*q.divisors.card*
        Real.sqrt (jointGcd q (-h) n : ℝ)) :=
      mul_le_mul_of_nonneg_left (unitSum_joint_uniform_bound q (-h) n) (by positivity)
    _ = _ := by ring

theorem jointGcd_le_second (q : ℕ) [NeZero q] (a b : ZMod q) :
    jointGcd q a b ≤ b.val.gcd q :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_right b.val (NeZero.pos q)) (Nat.gcd_dvd_right _ _)

end NField.Alignment.CommonResetTripleGcd
