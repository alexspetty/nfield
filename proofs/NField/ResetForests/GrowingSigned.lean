/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.GrowingRates
/-! # Signed forest and restoration rates for the stated growing window -/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open scoped BigOperators
open NField.Alignment AbsoluteForestWork SignedForestWork DedekindFourierMoment

theorem growing_forest_population {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      ((forestClocks (p-1) (returnDivisor p (L p))).card : ℝ) ≤ C*(p : ℝ)^ε := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := Core.incoming_divisor_small_power δ hδ
  obtain ⟨B, hB, hb⟩ := growing_triple_divisor_uniform hL δ hδ
  refine ⟨A*B, by positivity, ?_⟩
  intro p hp hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi : Core.incomingDivisorBudget (p-1) ≤ A*(p : ℝ)^(2*δ) :=
    (ha (p-1) (by omega)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) (by positivity)) hA.le)
  calc
    _ ≤ Core.incomingDivisorBudget (p-1)*(Core.tripleDivisorCount (returnDivisor p (L p)) : ℝ) :=
      forest_population_budget (by omega) (return_divisor_pos hp3 _)
    _ ≤ (A*(p : ℝ)^(2*δ))*(B*(p : ℝ)^δ) :=
      mul_le_mul hi (hb p hp.one_le) (Nat.cast_nonneg _) (by positivity)
    _ = (A*B)*((p : ℝ)^(2*δ)*(p : ℝ)^δ) := by ring
    _ = _ := by rw [← Real.rpow_add hpR]; congr 2; dsimp [δ]; ring

theorem growing_signed_and_restoration {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) (returnDivisor p (L p)))| ≤
        C*(p : ℝ)^(1+ε) ∧
      |restorationWork (p-1) (p^2) (returnDivisor p (L p))| ≤ C*(p : ℝ)^(1+ε) := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := growing_forest_population hL δ hδ
  let H : ℝ := 1+1/δ
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨A*H^2/2, by positivity, ?_⟩
  intro p hp hodd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p-1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hHN : (harmonic (p-1) : ℝ) ≤ H*(p : ℝ)^δ :=
    (harmonic_cast_mono (Nat.sub_le p 1)).trans
      (PhasePopulations.harmonic_small_power_from_mathlib δ hδ hp.one_le)
  have hb : (((p-1 : ℕ) : ℝ)/2)*((forestClocks (p-1) (returnDivisor p (L p))).card : ℝ)*
      (harmonic (p-1) : ℝ)^2 ≤ (A*H^2/2)*(p : ℝ)^(1+ε) := by
    calc
      _ ≤ ((p : ℝ)/2)*(A*(p : ℝ)^δ)*(H*(p : ℝ)^δ)^2 := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_right hN (by norm_num)) (ha p hp hodd)
            (Nat.cast_nonneg _) (by positivity)
        · exact pow_le_pow_left₀ hH0 hHN 2
        · positivity
        · positivity
      _ = (A*H^2/2)*((p : ℝ)*((p : ℝ)^δ*((p : ℝ)^δ)^2)) := by ring
      _ = (A*H^2/2)*(p : ℝ)^(1+δ+δ*2) := by
        rw [← Real.rpow_mul_natCast hpR.le]
        calc
          _ = (A*H^2/2)*((p : ℝ)^(1 : ℝ)*((p : ℝ)^δ*(p : ℝ)^(δ*2))) := by
            rw [Real.rpow_one]
            norm_num only [Nat.cast_ofNat]
          _ = _ := by rw [← Real.rpow_add hpR, ← Real.rpow_add hpR]; congr 2; ring
      _ = _ := by congr 2; dsimp [δ]; ring
  have hf := signed_forest_population_bound hp (returnDivisor p (L p))
  exact ⟨hf.1.trans hb, hf.2.trans hb⟩

theorem population_log_sampling_bound {p : ℕ} (hp : p.Prime) (D : ℕ) :
    |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2| ≤
      2*((forestClocks (p-1) D).card : ℝ)*(1+Real.log ((p-1 : ℕ) : ℝ))^2/(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hH := harmonic_le_one_add_log (p-1)
  have hN : ((p-1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ 4*((((p-1 : ℕ) : ℝ)/2)*((forestClocks (p-1) D).card : ℝ)*(harmonic (p-1) : ℝ)^2)/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (signed_forest_population_bound hp D).1 (by norm_num)) (sq_nonneg _)
    _ ≤ 4*(((p : ℝ)/2)*((forestClocks (p-1) D).card : ℝ)*(1+Real.log ((p-1 : ℕ) : ℝ))^2)/(p : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN (by norm_num)) (Nat.cast_nonneg _))
        (pow_le_pow_left₀ hH0 hH 2) (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end NField.ResetForests.ReturnWindows
