/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SignedForest
import NField.ResetForests.ForestRates
/-! # First-power signed forest and restoration rates

The actual forest population is controlled by the incoming divisor budget.
The finite signed clock bound retains the original coherent source and
therefore costs one power of the cutoff before the subpower factors.
-/

noncomputable section

namespace NField.ResetForests.SignedForestWork

open scoped BigOperators
open NField.Alignment
open AbsoluteForestWork DedekindFourierMoment

theorem forest_population_budget {N D : ℕ} (hN : 0 < N) (hD : 0 < D) :
    ((forestClocks N D).card : ℝ) ≤ Core.incomingDivisorBudget N*(Core.tripleDivisorCount D : ℝ) := by
  calc
    _ = ∑ _k ∈ forestClocks N D, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ forestClocks N D, (k.divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1; omega
      exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
    _ ≤ _ := forest_divisor_budget hN hD

theorem polynomial_forest_population (K C₀ ε : ℝ)
    (hK : 0 ≤ K) (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        ((forestClocks (p-1) D).card : ℝ) ≤ C*(p : ℝ)^ε := by
  let δ := ε/(K+2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := Core.incoming_divisor_small_power δ hδ
  obtain ⟨B, hB, hb⟩ := Core.triple_divisor_small_power δ hδ
  refine ⟨A*B*C₀^δ, by positivity, ?_⟩
  intro p D hp hD hheight
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : 0 < p-1 := by have := hp.two_le; omega
  have hi : Core.incomingDivisorBudget (p-1) ≤ A*(p : ℝ)^(2*δ) :=
    (ha (p-1) hN).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) (by positivity)) hA.le)
  have hd : (Core.tripleDivisorCount D : ℝ) ≤ (B*C₀^δ)*(p : ℝ)^(K*δ) := by
    calc
      _ ≤ B*(D : ℝ)^δ := hb D hD
      _ ≤ B*(C₀*(p : ℝ)^K)^δ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hheight hδ.le) hB.le
      _ = _ := by
        rw [Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_mul hpR.le]
        ring
  have he : (2*δ : ℝ)+K*δ=ε := by dsimp [δ]; field_simp; ring
  calc
    _ ≤ Core.incomingDivisorBudget (p-1)*(Core.tripleDivisorCount D : ℝ) :=
      forest_population_budget hN hD
    _ ≤ (A*(p : ℝ)^(2*δ))*((B*C₀^δ)*(p : ℝ)^(K*δ)) :=
      mul_le_mul hi hd (Nat.cast_nonneg _) (by positivity)
    _ = (A*B*C₀^δ)*((p : ℝ)^(2*δ)*(p : ℝ)^(K*δ)) := by ring
    _ = _ := by rw [← Real.rpow_add hpR, he]

theorem signed_forest_population_bound {p : ℕ} (hp : p.Prime) (D : ℕ) :
    |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤
      (((p-1 : ℕ) : ℝ)/2)*((forestClocks (p-1) D).card : ℝ)*(harmonic (p-1) : ℝ)^2 ∧
    |restorationWork (p-1) (p^2) D| ≤
      (((p-1 : ℕ) : ℝ)/2)*((forestClocks (p-1) D).card : ℝ)*(harmonic (p-1) : ℝ)^2 := by
  have hsum : (∑ d ∈ forestClocks (p-1) D, (harmonic (d/2) : ℝ)^2) ≤
      ((forestClocks (p-1) D).card : ℝ)*(harmonic (p-1) : ℝ)^2 := by
    calc
      _ ≤ ∑ _d ∈ forestClocks (p-1) D, (harmonic (p-1) : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
        have hH0 : (0 : ℝ) ≤ (harmonic (d/2) : ℝ) := by
          simpa using harmonic_cast_mono (Nat.zero_le (d/2))
        exact pow_le_pow_left₀ hH0
          (harmonic_cast_mono ((Nat.div_le_self d 2).trans hdN)) 2
      _ = _ := by simp
  have hf := signed_forest_and_restoration_finite hp D
  have hs := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ ((p-1 : ℕ) : ℝ)/2 by positivity)
  constructor
  · exact hf.1.trans (by simpa only [mul_assoc] using hs)
  · exact hf.2.trans (by simpa only [mul_assoc] using hs)

theorem polynomial_signed_and_restoration (K C₀ ε : ℝ)
    (hK : 0 ≤ K) (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤ C*(p : ℝ)^(1+ε) ∧
        |restorationWork (p-1) (p^2) D| ≤ C*(p : ℝ)^(1+ε) := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := polynomial_forest_population K C₀ δ hK hC₀ hδ
  let H : ℝ := 1+1/δ
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨A*H^2/2, by positivity, ?_⟩
  intro p D hp hD hheight
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p-1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hHN : (harmonic (p-1) : ℝ) ≤ H*(p : ℝ)^δ :=
    (harmonic_cast_mono (Nat.sub_le p 1)).trans
      (PhasePopulations.harmonic_small_power_from_mathlib δ hδ hp.one_le)
  have hb : (((p-1 : ℕ) : ℝ)/2)*((forestClocks (p-1) D).card : ℝ)*
      (harmonic (p-1) : ℝ)^2 ≤ (A*H^2/2)*(p : ℝ)^(1+ε) := by
    calc
      _ ≤ ((p : ℝ)/2)*(A*(p : ℝ)^δ)*(H*(p : ℝ)^δ)^2 := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_right hN (by norm_num)) (ha p D hp hD hheight)
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
          _ = _ := by
            rw [← Real.rpow_add hpR, ← Real.rpow_add hpR,
              show (1 : ℝ)+(δ+δ*2)=1+δ+δ*2 by ring]
      _ = _ := by congr 2; dsimp [δ]; ring
  have hf := signed_forest_population_bound hp D
  exact ⟨hf.1.trans hb, hf.2.trans hb⟩

theorem polynomial_signed_forest_estimate : Core.PolynomialForestSignedEstimate := by
  intro K C₀ ε hK hC₀ hε
  obtain ⟨C, hC, hc⟩ := polynomial_signed_and_restoration K C₀ ε hK hC₀ hε
  refine ⟨C, hC, ?_⟩
  intro p D hp _hodd hD hheight
  exact (hc p D hp hD hheight).1

theorem polynomial_signed_and_restoration_any_exponent (K C₀ ε : ℝ)
    (hC₀ : 0 < C₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤ C*(p : ℝ)^(1+ε) ∧
        |restorationWork (p-1) (p^2) D| ≤ C*(p : ℝ)^(1+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_signed_and_restoration (max K 0) C₀ ε
    (le_max_right _ _) hC₀ hε
  refine ⟨C, hC, ?_⟩
  intro p D hp hD hheight
  apply hc p D hp hD
  exact hheight.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ p)
      (le_max_left _ _)) hC₀.le)

end NField.ResetForests.SignedForestWork
