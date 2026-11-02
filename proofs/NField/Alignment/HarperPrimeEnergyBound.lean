/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothComparison
import Mathlib.NumberTheory.ZetaValues

/-!
# The actual prime and short-sum energy bounds

The proved Mertens prime-reciprocal estimate gives the leading constant one
in the prime energy. The prime-square correction is uniformly bounded by
the convergent reciprocal-square series. At the rounded cutoff the energy
is eventually at most (1+epsilon) log(log P), for every positive epsilon.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperPrimeEnergyBound

open scoped BigOperators
open Filter HarperPrimeProductMoment HarperSmoothDivisor HarperRoundedCutoff
  CollisionMertensInput MagnitudeShortComparison

theorem unitPrimeEnergy_nonneg (P : ℝ) : 0 ≤ unitPrimeEnergy P :=
  Finset.sum_nonneg fun p _ => add_nonneg
    (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (div_nonneg (by norm_num) (sq_nonneg _))

theorem prime_square_reciprocal_bound (P : ℝ) :
    (∑ p ∈ primesUpTo P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum (primesUpTo P) (fun _ _ => by positivity) hasSum_zeta_two

theorem unitPrimeEnergy_decomposition (P : ℝ) :
    unitPrimeEnergy P = (∑ p ∈ primesUpTo P, (1 : ℝ) / p) +
      6 * ∑ p ∈ primesUpTo P, (1 : ℝ) / (p : ℝ) ^ 2 := by
  unfold unitPrimeEnergy
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun p _ => by ring)

theorem unitPrimeEnergy_loglog_bound : ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P →
    unitPrimeEnergy P ≤ Real.log (Real.log P) + C := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨|C| + Real.pi ^ 2 + 1, by positivity, ?_⟩
  intro P hP
  have hh := (abs_le.mp (hC P hP)).2
  change (∑ p ∈ primesUpTo P, (1 : ℝ) / p) - Real.log (Real.log P) ≤ C at hh
  rw [unitPrimeEnergy_decomposition]
  nlinarith [prime_square_reciprocal_bound P, le_abs_self C]

theorem eventual_unitPrimeEnergy_bound {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      unitPrimeEnergy (primeCutoff x) ≤ (1 + epsilon) * Real.log (cutoffLog x) := by
  obtain ⟨C, _, hC⟩ := unitPrimeEnergy_loglog_bound
  filter_upwards [primeCutoff_tendsto.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop (C / epsilon)] with x hP hx
  have h := hC (primeCutoff x) hP
  rw [log_primeCutoff] at h
  have hsmall : C ≤ Real.log (cutoffLog x) * epsilon := (div_le_iff₀ he).mp hx
  nlinarith

theorem eventual_unitPrimeEnergy_five_fourths : ∀ᶠ x : ℝ in atTop,
    unitPrimeEnergy (primeCutoff x) ≤ (5 / 4 : ℝ) * Real.log (cutoffLog x) ∧
      2 * unitPrimeEnergy (primeCutoff x) ≤ (5 / 2 : ℝ) * Real.log (cutoffLog x) := by
  filter_upwards [eventual_unitPrimeEnergy_bound (by norm_num : (0 : ℝ) < 1 / 4)] with x h
  constructor <;> linarith

theorem shortEnergy_le_divisorSum (P : ℝ) (N : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1) :
    shortEnergy P (Finset.Icc 1 N) w ≤ smoothDivisorSum P (N : ℝ) := by
  unfold shortEnergy smoothDivisorSum
  rw [Nat.floor_natCast]
  apply Finset.sum_le_sum
  intro n hn
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg _) (hw n hn) : ‖w n‖ ^ 2 ≤ 1) (Nat.cast_nonneg (smoothDivisorCount P n))

theorem eventual_shortEnergy_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    ∀ w : ℕ → ℂ, (∀ n ∈ Finset.Icc 1 (p - 1), ‖w n‖ ≤ 1) →
      shortEnergy (primeCutoff x) (Finset.Icc 1 (p - 1)) w ≤ C * x * cutoffLog x := by
  obtain ⟨C, hC, hb⟩ := prime_square_smooth_divisor_estimate
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with p hp hge
  dsimp only at hp ⊢
  intro w hw
  have h := shortEnergy_le_divisorSum (primeCutoff ((p : ℝ) - 1)) (p - 1) w hw
  rw [Nat.cast_sub hge, Nat.cast_one] at h
  exact h.trans (hp.1.trans hp.2)

end NField.Alignment.HarperPrimeEnergyBound
