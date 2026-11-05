/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLocalFactorLosses
import NField.Alignment.CollisionPrimeDistribution

/-!
# Exact lcm exponents and their pointwise losses

The exponent is the factorization of the actual cutoff period. Its equality
to the natural logarithm and to the floor of the real logarithm is explicit.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmPrimeLosses

open CollisionOdometerRecurrence CollisionPrimeDistribution CollisionLocalFactorLosses
open CollisionResetLocalFactors CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

def lcmPrimePowerLoss (m p : ℕ) : ℝ := ((p : ℝ)⁻¹)^(p.log m+1)

theorem cutoffPeriod_prime_exponent (m : ℕ) {p : ℕ} (hp : p.Prime) :
    (cutoffPeriod m).factorization p=p.log m := by
  rw [cutoffPeriod_eq_lcmUpto,Nat.factorization_lcmUpto m hp]

theorem cutoffPeriod_prime_exponent_floor (m : ℕ) {p : ℕ} (hp : p.Prime) :
    (cutoffPeriod m).factorization p=⌊Real.log m/Real.log p⌋₊ := by
  rw [cutoffPeriod_prime_exponent m hp,← Real.natFloor_logb_natCast,Real.logb]

theorem cutoffPeriod_primeFactors (m : ℕ) : (cutoffPeriod m).primeFactors=Nat.primesLE m := by
  rw [cutoffPeriod_eq_lcmUpto,Nat.primeFactors_lcmUpto]

theorem lcmPrimePowerLoss_nonneg (m p : ℕ) : 0 ≤ lcmPrimePowerLoss m p := by
  unfold lcmPrimePowerLoss
  positivity

theorem lcmPrimePowerLoss_bound {m p : ℕ} (hp : p.Prime) (hpm : p ≤ m) :
    lcmPrimePowerLoss m p ≤ 1/(m : ℝ) ∧ lcmPrimePowerLoss m p ≤ 1/(p : ℝ)^2 := by
  have hm0 : 0 < m := hp.pos.trans_le hpm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hv : 1 ≤ p.log m := (Nat.le_log_iff_pow_le hp.one_lt hm0.ne').mpr (by simpa using hpm)
  have hnext : (m : ℝ) < (p : ℝ)^(p.log m+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt m
  unfold lcmPrimePowerLoss
  rw [inv_pow,← one_div]
  constructor
  · exact one_div_le_one_div_of_le hmR hnext.le
  · exact one_div_le_one_div_of_le (sq_pos_of_pos hpR)
      (pow_le_pow_right₀ hp1 (by omega : 2 ≤ p.log m+1))

theorem lcm_logarithmic_multiplier_bound {m p : ℕ} (hp : p.Prime) (hpm : p ≤ m) :
    ((p.log m : ℝ)+2)*Real.log p ≤ 3*Real.log m := by
  have hm0 : 0 < m := hp.pos.trans_le hpm
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow : (p : ℝ)^(p.log m) ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p hm0.ne'
  have hlogpow := Real.log_le_log (pow_pos hpR _) hpow
  rw [Real.log_pow] at hlogpow
  have hlog := Real.log_le_log hpR (by exact_mod_cast hpm : (p : ℝ) ≤ (m : ℝ))
  nlinarith

theorem lcm_alignment_average_loss {m p : ℕ} (hp : p.Prime) (hpm : p ≤ m) :
    (1/((p : ℝ)-1)-alignmentPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p))*Real.log p ≤
      3*Real.log m*lcmPrimePowerLoss m p := by
  rw [cutoffPeriod_prime_exponent m hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  calc
    _ ≤ (((p.log m : ℝ)+2)*((p : ℝ)⁻¹)^(p.log m+1))*Real.log p :=
      mul_le_mul_of_nonneg_right (alignmentPrimeAverage_loss_bound hp2 _).2 hl
    _ = (((p.log m : ℝ)+2)*Real.log p)*lcmPrimePowerLoss m p := by
      unfold lcmPrimePowerLoss
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (lcm_logarithmic_multiplier_bound hp hpm)
      (lcmPrimePowerLoss_nonneg m p)

theorem lcm_reset_average_loss {m p : ℕ} (hp : p.Prime) (hpm : p ≤ m) :
    (1/((p : ℝ)-1)-resetPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p))*Real.log p ≤
      3*Real.log m*lcmPrimePowerLoss m p := by
  rw [cutoffPeriod_prime_exponent m hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  calc
    _ ≤ (((p.log m : ℝ)+2)*((p : ℝ)⁻¹)^(p.log m+1))*Real.log p :=
      mul_le_mul_of_nonneg_right (resetPrimeAverage_loss_bound hp2 _).2 hl
    _ = (((p.log m : ℝ)+2)*Real.log p)*lcmPrimePowerLoss m p := by
      unfold lcmPrimePowerLoss
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (lcm_logarithmic_multiplier_bound hp hpm)
      (lcmPrimePowerLoss_nonneg m p)

end NField.Alignment.CollisionLcmPrimeLosses
