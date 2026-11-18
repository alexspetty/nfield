/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestFactors
import NField.ResetForests.GridWork
/-! # Absolute work of the actual complete reset forest

Every selected denominator keeps the complete cutoff field. The exact
incoming/surviving pair bounds its divisor weight before the arithmetic
small-power estimate is applied.
-/

noncomputable section

namespace NField.ResetForests.AbsoluteForestWork

open scoped BigOperators
open NField.Alignment
open CollisionRampEnergy DedekindFourierMoment

theorem forest_absolute_divisor_budget {N D : ℕ} (hN : 0 < N) (hD : 0 < D) (Q : ℕ) :
    Core.absoluteForestReading N Q D ≤
      ((N : ℝ)/2*Real.sqrt (N : ℝ)*(harmonic N : ℝ))*
        (Core.incomingDivisorBudget N*(Core.tripleDivisorCount D : ℝ)) := by
  have hHN : (0 : ℝ) ≤ (harmonic N : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le N)
  have hreading : Core.absoluteForestReading N Q D =
      ∑ k ∈ forestClocks N D, ((N/k : ℕ) : ℝ)*
        ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
          |boundaryResponse N ((a : ℝ)/(k : ℝ))*midpointRow Q ((a : ℝ)/(k : ℝ))| := by
    simp [Core.absoluteForestReading, Core.forestMask, forestClocks, Finset.sum_filter]
  rw [hreading]
  calc
    _ ≤ ∑ k ∈ forestClocks N D,
        ((N : ℝ)/2*Real.sqrt (N : ℝ)*(harmonic N : ℝ))*(k.divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hHk : (0 : ℝ) ≤ (harmonic k : ℝ) := by
        simpa using harmonic_cast_mono (Nat.zero_le k)
      have hs : Real.sqrt (k : ℝ) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt (Nat.cast_le.mpr hkN)
      have hH : (harmonic k : ℝ) ≤ (harmonic N : ℝ) := harmonic_cast_mono hkN
      calc
        _ ≤ (N : ℝ)/2*Real.sqrt (k : ℝ)*(k.divisors.card : ℝ)*(harmonic k : ℝ) :=
          ResetGrid.coherent_reset_absolute_bound N Q hk2
        _ ≤ (N : ℝ)/2*Real.sqrt (N : ℝ)*(k.divisors.card : ℝ)*(harmonic N : ℝ) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (Nat.cast_nonneg _))
            hH hHk (by positivity)
        _ = _ := by ring
    _ = ((N : ℝ)/2*Real.sqrt (N : ℝ)*(harmonic N : ℝ))*
        (∑ k ∈ forestClocks N D, (k.divisors.card : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (forest_divisor_budget hN hD) (by positivity)

/-- The finite forest bound holds for every sampler, with the original cutoff field. -/
theorem whole_forest_absolute_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q D : ℕ, 0 < N → 0 < D →
      Core.absoluteForestReading N Q D ≤
        (C/2)*(N : ℝ)^(3/2+2*η)*(harmonic N : ℝ)*(Core.tripleDivisorCount D : ℝ) := by
  obtain ⟨C, hC, hc⟩ := Core.incoming_divisor_small_power η hη
  refine ⟨C, hC, ?_⟩
  intro N Q D hN hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHN : (0 : ℝ) ≤ (harmonic N : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le N)
  have hpow : (N : ℝ)*Real.sqrt (N : ℝ)*(N : ℝ)^(2*η) = (N : ℝ)^(3/2+2*η) := by
    calc
      _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^(1/2 : ℝ)*(N : ℝ)^(2*η) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = (N : ℝ)^((1 : ℝ)+1/2+2*η) := by rw [← Real.rpow_add hNR, ← Real.rpow_add hNR]
      _ = _ := by congr 1; ring
  calc
    _ ≤ ((N : ℝ)/2*Real.sqrt (N : ℝ)*(harmonic N : ℝ))*
        (Core.incomingDivisorBudget N*(Core.tripleDivisorCount D : ℝ)) :=
      forest_absolute_divisor_budget hN hD Q
    _ ≤ ((N : ℝ)/2*Real.sqrt (N : ℝ)*(harmonic N : ℝ))*
        ((C*(N : ℝ)^(2*η))*(Core.tripleDivisorCount D : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hc N hN) (Nat.cast_nonneg _)) (by positivity)
    _ = (C/2)*((N : ℝ)*Real.sqrt (N : ℝ)*(N : ℝ)^(2*η))*
        (harmonic N : ℝ)*(Core.tripleDivisorCount D : ℝ) := by ring
    _ = _ := by rw [hpow]

theorem whole_forest_absolute_estimate : Core.WholeForestAbsoluteEstimate := by
  intro η hη
  obtain ⟨C, hC, hc⟩ := whole_forest_absolute_bound η hη
  refine ⟨C, hC, ?_⟩
  intro p D hp _hodd hD
  exact hc (p-1) (p^2) D (by have := hp.two_le; omega) hD

end NField.ResetForests.AbsoluteForestWork
