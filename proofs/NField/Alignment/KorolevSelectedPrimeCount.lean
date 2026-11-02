/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowMass
import NField.Alignment.KorolevMissingPrimeDecay

/-!
# Actual selected-window missing-prime count

The mass of the disjoint U/V windows is proved, not assumed. The remaining
conditions are explicit size, index and cutoff conditions, which must still
be derived from the source's asymptotic choices before its Lemma A closes.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSelectedPrimeCount
open scoped BigOperators Topology Classical
open Filter KorolevPrimeWindows KorolevWindowMass KorolevMissingPrimeCount
  KorolevMissingPrimeDecay HarperRoundedCutoff

theorem window_endpoints_source {m : ℝ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k) :
    upperEndpoint (Real.log m) k = m ^ (1/(2*(k : ℝ)-1))/4 ∧
      lowerEndpoint (Real.log m) k = m ^ (1/(2*(k : ℝ)-1)-1/(4*(k : ℝ)^2-1)) :=
  ⟨upperEndpoint_source hm k, lowerEndpoint_source hm hk⟩

theorem eventual_selected_avoid_count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (L : ℝ) (a b : ℕ), 1 ≤ a → a ≤ b →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L → upperEndpoint L a ≤ smoothCutoff x → ∀ m : ℕ,
        (((avoidSet x (selectedPrimes L a b)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          C * (x/(Real.log x * Real.log (Real.log x)) + x*Real.log (Real.log x) *
            Real.exp (lossConstant*((b : ℝ)+1)^2/L - (Real.log ((b : ℝ)+1)-Real.log a)/2)) := by
  obtain ⟨C, hC, h⟩ := eventual_coprime_avoid_count_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (0 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hx hx0 hu L a b ha hab hsize hcut m
  dsimp only [Function.comp_apply] at hu
  have hL : 0 < L := (window_conditions (k := b+1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsize)).1
  have hS := selected_subset (b := b) hL.le ha hcut
  have hm := selected_mass_lower ha hab hsize
  have he := Real.exp_le_exp.mpr (show -(∑ p ∈ selectedPrimes L a b, (1 : ℝ)/p) ≤
    lossConstant*((b : ℝ)+1)^2/L - (Real.log ((b : ℝ)+1)-Real.log a)/2 by linarith)
  apply (hx _ hS m).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left he (mul_nonneg hx0 hu))) hC.le

theorem eventual_contiguous_avoid_count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (L : ℝ) (a b : ℕ), 1 ≤ a → a ≤ b →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L → upperEndpoint L a ≤ smoothCutoff x → ∀ m : ℕ,
        (((avoidSet x (KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (b+1))
          (upperEndpoint L a))).filter (fun n => n.Coprime m)).card : ℝ) ≤
          C * (x/(Real.log x * Real.log (Real.log x)) + x*Real.log (Real.log x) *
            Real.exp (12*KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/L -
              (Real.log ((b : ℝ)+1)-Real.log a))) := by
  obtain ⟨C, hC, h⟩ := eventual_coprime_avoid_count_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (0 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hx hx0 hu L a b ha hab hsize hcut m
  dsimp only [Function.comp_apply] at hu
  have hS : KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (b+1)) (upperEndpoint L a) ⊆
      CollisionMertensInput.primesUpTo (smoothCutoff x) := by
    intro p hp
    obtain ⟨hpp, _, hpU⟩ := KorolevPrimeIntervals.intervalPrimes_mem.mp hp
    exact CollisionMertensInput.primesUpTo_mem.mpr ⟨hpp, hpU.trans hcut⟩
  have hm := contiguous_mass_lower ha hab hsize
  have he := Real.exp_le_exp.mpr (show
    -(∑ p ∈ KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (b+1)) (upperEndpoint L a), (1 : ℝ)/p) ≤
      12*KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/L -
        (Real.log ((b : ℝ)+1)-Real.log a) by linarith)
  apply (hx _ hS m).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left he (mul_nonneg hx0 hu))) hC.le

end NField.Alignment.KorolevSelectedPrimeCount
