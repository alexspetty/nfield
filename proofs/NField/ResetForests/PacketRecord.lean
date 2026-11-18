/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RecordPairs
/-! # The complete record of actual reset masses and detector readings

Every source coefficient remains arbitrary. A resetting mass is its actual
divisor sum, rather than the load of the coherent source.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketQueries

open scoped BigOperators Matrix
open NField.Alignment CollisionRampEnergy CommonResetGram CommonResetWeightedSources SourceMetrics QuadraticResponse

def resetRow (N k : ℕ) (j : Fin N) : ℝ := if k ∣ j.val + 1 then 1 else 0
def detectorRow (N Q k : ℕ) (j : Fin N) : ℝ :=
  2 * ∑ a ∈ BranchTransport.unitAddresses k,
    midpointRow (j.val + 1) ((a : ℝ) / (k : ℝ)) * midpointRow Q ((a : ℝ) / (k : ℝ))
def packetRecord {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) : Matrix (RecordIndex t) (Fin N) ℝ :=
  fun i j => if i.2 then detectorRow N Q (κ i.1) j else resetRow N (κ i.1) j
def pullbackQuery {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Aᵀ * (pairQuery t * A)
def packetQuery {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (c : Fin N → ℝ) : ℝ :=
  4 * ∑ i : Fin t, resetWeight N (cutoffCoefficients N c) (κ i) *
    ∑ a ∈ BranchTransport.unitAddresses (κ i),
      weightedProfile N (cutoffCoefficients N c) ((a : ℝ) / (κ i : ℝ)) *
        midpointRow Q ((a : ℝ) / (κ i : ℝ))
def packetCovector {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) : Fin N → ℝ :=
  pullbackQuery (packetRecord N Q κ) *ᵥ (fun _ => 1)

theorem reset_row_reading (N k : ℕ) (c : Fin N → ℝ) :
    resetRow N k ⬝ᵥ c = resetWeight N (cutoffCoefficients N c) k := by
  rw [resetWeight, sum_source_indices]
  simp only [dotProduct, resetRow, cutoff_coefficients_succ]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem detector_row_reading (N Q k : ℕ) (c : Fin N → ℝ) :
    detectorRow N Q k ⬝ᵥ c =
      ∑ a ∈ BranchTransport.unitAddresses k,
        weightedProfile N (cutoffCoefficients N c) ((a : ℝ) / (k : ℝ)) *
          midpointRow Q ((a : ℝ) / (k : ℝ)) := by
  simp only [detectorRow, dotProduct, weighted_profile_fin, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem record_reset_row {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (c : Fin N → ℝ) (i : Fin t) :
    (packetRecord N Q κ *ᵥ c) (i, false) = resetWeight N (cutoffCoefficients N c) (κ i) := by
  change resetRow N (κ i) ⬝ᵥ c = _
  exact reset_row_reading N (κ i) c

theorem record_detector_row {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (c : Fin N → ℝ) (i : Fin t) :
    (packetRecord N Q κ *ᵥ c) (i, true) =
      ∑ a ∈ BranchTransport.unitAddresses (κ i),
        weightedProfile N (cutoffCoefficients N c) ((a : ℝ) / (κ i : ℝ)) *
          midpointRow Q ((a : ℝ) / (κ i : ℝ)) := by
  change detectorRow N Q (κ i) ⬝ᵥ c = _
  exact detector_row_reading N Q (κ i) c

theorem pullback_query_quadratic {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ) (c : Fin N → ℝ) :
    c ⬝ᵥ (pullbackQuery A *ᵥ c) = (A *ᵥ c) ⬝ᵥ (pairQuery t *ᵥ (A *ᵥ c)) := by
  unfold pullbackQuery
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem packet_record_quadratic {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (c : Fin N → ℝ) :
    packetQuery N Q κ c = c ⬝ᵥ (pullbackQuery (packetRecord N Q κ) *ᵥ c) := by
  rw [pullback_query_quadratic, pair_query_quadratic]
  simp_rw [record_reset_row, record_detector_row]
  rfl

theorem pullback_query_symmetric {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ) :
    (pullbackQuery A)ᵀ = pullbackQuery A := by
  simp only [pullbackQuery, Matrix.transpose_mul, Matrix.transpose_transpose,
    pair_query_symmetric, Matrix.mul_assoc]

theorem pullback_query_entry {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ) (i j : Fin N) :
    pullbackQuery A i j = 2 * ∑ l : Fin t,
      (A (l, false) i * A (l, true) j + A (l, true) i * A (l, false) j) := by
  change (∑ r : RecordIndex t, A r i * (pairQuery t *ᵥ fun s => A s j) r) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pair_query_mulVec,
    Bool.not_false, Bool.not_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem detector_row_zero_on_reset {N Q k : ℕ} (j : Fin N) (hd : k ∣ j.val + 1) :
    detectorRow N Q k j = 0 := by
  have hf (a : ℕ) : Int.fract (((j.val + 1 : ℕ) : ℝ) * ((a : ℝ) / (k : ℝ))) = 0 := by
    have h := BranchTransport.frequency_fract_congr (K := j.val + 1) (Q := 0)
      (by simpa using Nat.mod_eq_zero_of_dvd hd) a
    simpa using h
  unfold detectorRow
  have hsum : (∑ a ∈ BranchTransport.unitAddresses k,
      midpointRow (j.val + 1) ((a : ℝ) / (k : ℝ)) * midpointRow Q ((a : ℝ) / (k : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hw : midpointRow (j.val + 1) ((a : ℝ) / (k : ℝ)) = 0 := by
      unfold midpointRow
      exact if_pos (hf a)
    rw [hw, zero_mul]
  rw [hsum, mul_zero]

theorem reset_detector_column_zero (N Q k : ℕ) (j : Fin N) :
    resetRow N k j * detectorRow N Q k j = 0 := by
  by_cases hd : k ∣ j.val + 1
  · rw [detector_row_zero_on_reset j hd, mul_zero]
  · simp only [resetRow, if_neg hd, zero_mul]

theorem packet_query_zero_diagonal {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (j : Fin N) :
    pullbackQuery (packetRecord N Q κ) j j = 0 := by
  rw [pullback_query_entry]
  have hsum : (∑ l : Fin t,
      (packetRecord N Q κ (l, false) j * packetRecord N Q κ (l, true) j +
        packetRecord N Q κ (l, true) j * packetRecord N Q κ (l, false) j)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    simp only [packetRecord, Bool.false_eq_true, if_false, if_true]
    rw [mul_comm (detectorRow N Q (κ l) j), reset_detector_column_zero, add_zero]
  rw [hsum, mul_zero]

theorem packet_query_hasFDerivAt {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) (c : Fin N → ℝ) :
    HasFDerivAt (packetQuery N Q κ)
      ((2 : ℝ) • sourceCovector N (pullbackQuery (packetRecord N Q κ) *ᵥ c)) c := by
  have he : packetQuery N Q κ = fun c => c ⬝ᵥ (pullbackQuery (packetRecord N Q κ) *ᵥ c) :=
    funext (packet_record_quadratic N Q κ)
  rw [he]
  apply symmetric_quadratic_hasFDerivAt
  intro i j
  exact congrFun (congrFun (pullback_query_symmetric (packetRecord N Q κ)).symm i) j

theorem coherent_packet_derivative {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) :
    fderiv ℝ (packetQuery N Q κ) (fun _ => 1) = (2 : ℝ) • sourceCovector N (packetCovector N Q κ) :=
  (packet_query_hasFDerivAt N Q κ (fun _ => 1)).fderiv

end NField.ResetForests.PacketQueries
