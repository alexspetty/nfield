/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestWork
import NField.ResetForests.PhaseCells
/-! # Polynomial-height forest work at the printed scales

The divisor and harmonic small-power estimates are proved inputs. Choosing
their exponents explicitly yields the absolute and normalized forest rates.
-/

noncomputable section

namespace NField.ResetForests.AbsoluteForestWork

open scoped BigOperators
open NField.Alignment
open DedekindFourierMoment

theorem polynomial_forest_absolute_bound (K C₀ ε : ℝ)
    (hK : 0 ≤ K) (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        Core.absoluteForestReading (p-1) (p^2) D ≤ C*(p : ℝ)^(3/2+ε) := by
  let δ := ε/(K+3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := whole_forest_absolute_bound δ hδ
  obtain ⟨B, hB, hb⟩ := Core.triple_divisor_small_power δ hδ
  let H : ℝ := 1+1/δ
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨(A/2)*H*B*C₀^δ, by positivity, ?_⟩
  intro p D hp hD hheight
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : 0 < p-1 := by have := hp.two_le; omega
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hHN : (harmonic (p-1) : ℝ) ≤ H*(p : ℝ)^δ :=
    (harmonic_cast_mono (Nat.sub_le p 1)).trans
      (PhasePopulations.harmonic_small_power_from_mathlib δ hδ hp.one_le)
  have hpower : (((p-1 : ℕ) : ℝ))^(3/2+2*δ) ≤ (p : ℝ)^(3/2+2*δ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) (by positivity)
  have hDpower : (D : ℝ)^δ ≤ C₀^δ*(p : ℝ)^(K*δ) := by
    calc
      _ ≤ (C₀*(p : ℝ)^K)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _) hheight hδ.le
      _ = _ := by
        rw [Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_mul hpR.le]
  have hτ : (Core.tripleDivisorCount D : ℝ) ≤ (B*C₀^δ)*(p : ℝ)^(K*δ) := by
    calc
      _ ≤ B*(D : ℝ)^δ := hb D hD
      _ ≤ B*(C₀^δ*(p : ℝ)^(K*δ)) := mul_le_mul_of_nonneg_left hDpower hB.le
      _ = _ := by ring
  have hexp : (3/2+2*δ : ℝ)+δ+K*δ=3/2+ε := by
    dsimp [δ]
    field_simp
    ring
  calc
    _ ≤ (A/2)*(((p-1 : ℕ) : ℝ))^(3/2+2*δ)*
        (harmonic (p-1) : ℝ)*(Core.tripleDivisorCount D : ℝ) := ha (p-1) (p^2) D hN hD
    _ ≤ (A/2)*(p : ℝ)^(3/2+2*δ)*(H*(p : ℝ)^δ)*
        ((B*C₀^δ)*(p : ℝ)^(K*δ)) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (by positivity)) hHN hH0 (by positivity)
      · exact hτ
      · exact Nat.cast_nonneg _
      · positivity
    _ = ((A/2)*H*B*C₀^δ)*
        (((p : ℝ)^(3/2+2*δ)*(p : ℝ)^δ)*(p : ℝ)^(K*δ)) := by ring
    _ = _ := by rw [← Real.rpow_add hpR, ← Real.rpow_add hpR, hexp]

theorem selected_forest_abs_le (N Q D : ℕ) :
    |Core.selectedReading N Q (Core.forestMask N D)| ≤ Core.absoluteForestReading N Q D := by
  have hclock (k : ℕ) : |Core.clockReading N Q k| ≤ ((N/k : ℕ) : ℝ)*
      ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        |CollisionRampEnergy.boundaryResponse N ((a : ℝ)/(k : ℝ))*
          CollisionRampEnergy.midpointRow Q ((a : ℝ)/(k : ℝ))| := by
    unfold Core.clockReading
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N/k : ℕ) from Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
  unfold Core.selectedReading Core.absoluteForestReading
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 N,
        |if Core.forestMask N D k then Core.clockReading N Q k else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      cases Core.forestMask N D k
      · simp
      · simpa using hclock k

/-- The normalized signed forest contribution has the printed half-power bound. -/
theorem polynomial_forest_sampling_bound (K C₀ ε : ℝ)
    (hK : 0 ≤ K) (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2| ≤
          C*(p : ℝ)^(-1/2+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_forest_absolute_bound K C₀ ε hK hC₀ hε
  refine ⟨4*C, by positivity, ?_⟩
  intro p D hp hD hheight
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    _ = 4*|Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)|/(p : ℝ)^2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
      norm_num
    _ ≤ 4*Core.absoluteForestReading (p-1) (p^2) D/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (selected_forest_abs_le _ _ _) (by norm_num)) (sq_nonneg _)
    _ ≤ 4*(C*(p : ℝ)^(3/2+ε))/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc p D hp hD hheight) (by norm_num)) (sq_nonneg _)
    _ = _ := by
      rw [show 4*(C*(p : ℝ)^(3/2+ε))/(p : ℝ)^2=(4*C)*((p : ℝ)^(3/2+ε)/(p : ℝ)^2) by ring,
        ← Real.rpow_two, ← Real.rpow_sub hpR,
        show (3/2+ε : ℝ)-2=-1/2+ε by ring]

theorem polynomial_forest_absolute_any_exponent (K C₀ ε : ℝ)
    (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        Core.absoluteForestReading (p-1) (p^2) D ≤ C*(p : ℝ)^(3/2+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_forest_absolute_bound (max K 0) C₀ ε
    (le_max_right _ _) hC₀ hε
  refine ⟨C, hC, ?_⟩
  intro p D hp hD hheight
  apply hc p D hp hD
  exact hheight.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ p)
      (le_max_left _ _)) hC₀.le)

theorem polynomial_forest_sampling_any_exponent (K C₀ ε : ℝ)
    (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)/(p : ℝ)^2| ≤
          C*(p : ℝ)^(-1/2+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_forest_sampling_bound (max K 0) C₀ ε
    (le_max_right _ _) hC₀ hε
  refine ⟨C, hC, ?_⟩
  intro p D hp hD hheight
  apply hc p D hp hD
  exact hheight.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ p)
      (le_max_left _ _)) hC₀.le)

end NField.ResetForests.AbsoluteForestWork
