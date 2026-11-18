/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestFactors
import NField.ResetForests.OrderedWork
/-! # A finite carrier for the actual reset forest

The carrier N^N D represents precisely the same selected denominators up
to N. It is used only for source reconstruction, never as the polynomial
height parameter in an analytic estimate.
-/

noncomputable section

namespace NField.ResetForests.SignedForestWork

open scoped BigOperators
open NField.Alignment
open AbsoluteForestWork

def forestCarrier (N D : ℕ) : ℕ := N^N*D

theorem incoming_dvd_base_power {N k : ℕ} (hN : 0 < N)
    (hk : 0 < k) (hkN : k ≤ N) : incomingPart N k ∣ N^N := by
  have hi := (incoming_rough_positive N hk).1
  have hiN := (Nat.le_of_dvd hk (incoming_part_dvd N hk.ne')).trans hkN
  apply (Nat.factorization_le_iff_dvd hi.ne' (pow_ne_zero _ hN.ne')).mp
  rw [Nat.factorization_pow]
  intro q
  by_cases hq0 : (incomingPart N k).factorization q=0
  · simp [hq0]
  · have hmem : q ∈ (incomingPart N k).primeFactors := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hq0
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hqN := incoming_prime_dvd_base hprime (Nat.dvd_of_mem_primeFactors hmem)
    have hNq := hprime.factorization_pos_of_dvd hN.ne' hqN
    have hsmall := Nat.factorization_lt q hi.ne'
    simp only [Finsupp.nsmul_apply, nsmul_eq_mul]
    nlinarith

theorem forest_carrier_selection {N k : ℕ} (hN : 0 < N)
    (hk : 0 < k) (hkN : k ≤ N) (D : ℕ) :
    Core.roughPart N k ∣ D ↔ k ∣ forestCarrier N D := by
  constructor
  · intro hr
    have hd := Nat.mul_dvd_mul (incoming_dvd_base_power hN hk hkN) hr
    rw [incoming_rough_product N hk.ne'] at hd
    exact hd
  · intro hkD
    have hrD : Core.roughPart N k ∣ N^N*D := (rough_part_dvd N hk.ne').trans hkD
    exact ((rough_part_coprime_base N k).pow_right N).dvd_mul_left.mp hrD

theorem forest_mask_carrier {N k : ℕ} (hN : 0 < N)
    (hk : 0 < k) (hkN : k ≤ N) (D : ℕ) :
    Core.forestMask N D k=decide (k ∣ forestCarrier N D) := by
  unfold Core.forestMask
  simp only [forest_carrier_selection hN hk hkN]

theorem selected_forest_saturated {N : ℕ} (hN : 0 < N) (Q D : ℕ) :
    Core.selectedReading N Q (Core.forestMask N D) =
      Core.saturatedBoundary N Q (forestCarrier N D) (fun _ => 1) := by
  unfold Core.selectedReading Core.saturatedBoundary
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
  rw [forest_mask_carrier hN (by omega : 0 < k) hkN]
  rw [Core.unit_reset_mass, CommonResetGram.unit_weights]
  simp only [Core.clockReading, decide_eq_true_eq]

theorem selected_forest_complete_source {N : ℕ} (hN : 0 < N) (Q D : ℕ) :
    Core.selectedReading N Q (Core.forestMask N D) =
      2*∑ d ∈ Finset.Icc 1 N,
        Core.collapseSource N (forestCarrier N D) (fun _ => 1) d*
          (∑ j ∈ Finset.Icc 1 N, Core.completeCorrelation Q j d) := by
  rw [selected_forest_saturated hN,
    Core.saturated_boundary_coefficients]
  simp only [mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Core.completeCorrelation, CommonResetBernoulliLifts.coefficient_swap]

end NField.ResetForests.SignedForestWork
