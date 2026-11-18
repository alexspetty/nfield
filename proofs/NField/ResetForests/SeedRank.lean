/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SeedData
/-! # Full rank of the literal seed record, with all thirty source columns -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.SeedRecord

open scoped BigOperators Matrix
open PacketQueries

theorem paired_record_full_row_rank {N t : ℕ}
    (A : Matrix (RecordIndex t) (Fin N) ℝ) (low clock : Fin t → Fin N)
    (hzero : ∀ i j, A (i, false) (low j) = 0)
    (hclock : ∀ i j, A (i, false) (clock j) = if i = j then 1 else 0)
    (hdet : Matrix.det (fun i j => A (i, true) (low j)) ≠ 0) : A.rank = 2 * t := by
  let D : Matrix (Fin t) (Fin t) ℝ := fun i j => A (i, true) (low j)
  have hdi : Function.Injective Dᵀ.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det Dᵀ).mpr
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdet
  have hkernel (z : RecordIndex t → ℝ) (hz : Aᵀ *ᵥ z = 0) : z = 0 := by
    have hd : Dᵀ *ᵥ (fun i => z (i, true)) = 0 := by
      ext j
      have he := congrFun hz (low j)
      simpa only [D, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, hzero, zero_mul, zero_add, add_zero,
        Pi.zero_apply] using he
    have ht : (fun i => z (i, true)) = 0 := hdi (by rw [hd, Matrix.mulVec_zero])
    have htrue (i : Fin t) : z (i, true) = 0 := congrFun ht i
    have hfalse (j : Fin t) : z (j, false) = 0 := by
      have he := congrFun hz (clock j)
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fintype.sum_prod_type, Fintype.sum_bool] at he
      simpa [hclock, htrue] using he
    ext ⟨i, b⟩
    cases b
    · exact hfalse i
    · exact htrue i
  have hi : Function.Injective Aᵀ.mulVecLin := by
    intro x y he
    change Aᵀ *ᵥ x = Aᵀ *ᵥ y at he
    have hz : Aᵀ *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
    exact sub_eq_zero.mp (hkernel _ hz)
  have hr := LinearMap.finrank_range_of_inj hi
  change Aᵀ.rank = Module.finrank ℝ (RecordIndex t → ℝ) at hr
  rw [Matrix.rank_transpose, Module.finrank_pi, record_index_card] at hr
  exact hr

def seedLowColumn (j : Fin 5) : Fin 30 := ⟨j.val, by omega⟩
def packetLowColumn (j : Fin 3) : Fin 30 := ⟨j.val, by omega⟩
def seedClockColumn (i : Fin 5) : Fin 30 := ⟨seedClocks i - 1, by fin_cases i <;> decide⟩
def packetClockColumn (i : Fin 3) : Fin 30 := ⟨packetClocks i - 1, by fin_cases i <;> decide⟩

theorem seed_clock_positive (i : Fin 5) : 0 < seedClocks i := by
  fin_cases i <;> decide

theorem packet_clock_positive (i : Fin 3) : 0 < packetClocks i := by
  fin_cases i <;> decide

theorem fringe_clock_positive (i : Fin 2) : 0 < fringeClocks i := by
  fin_cases i <;> decide

theorem seed_low_detector :
    (fun i j => seedRecord (i, true) (seedLowColumn j)) = seedDetectorTable.map (fun x => (x : ℝ)) := by
  ext i j
  change detectorRow 30 961 (seedClocks i) (seedLowColumn j) = (seedDetectorTable i j : ℝ)
  rw [detector_row_rational (seed_clock_positive i)]
  exact congrArg (fun x : ℚ => (x : ℝ)) (congrFun (congrFun seed_table_exact i) j)

theorem packet_low_detector :
    (fun i j => seedPacketRecord (i, true) (packetLowColumn j)) =
      seedPacketMinor.map (fun x => (x : ℝ)) := by
  ext i j
  change detectorRow 30 961 (packetClocks i) (packetLowColumn j) = (seedPacketMinor i j : ℝ)
  rw [detector_row_rational (packet_clock_positive i)]
  exact congrArg (fun x : ℚ => (x : ℝ)) (congrFun (congrFun seed_packet_minor_exact i) j)

theorem seed_actual_determinant :
    Matrix.det (fun i j => seedRecord (i, true) (seedLowColumn j)) = (-88076/216315 : ℝ) := by
  rw [seed_low_detector, ← Rat.cast_det, seed_detector_determinant]
  norm_num

theorem packet_actual_determinant :
    Matrix.det (fun i j => seedPacketRecord (i, true) (packetLowColumn j)) = (-548/4807 : ℝ) := by
  rw [packet_low_detector, ← Rat.cast_det, seed_packet_determinant]
  norm_num

theorem seed_reset_low (i j : Fin 5) : seedRecord (i, false) (seedLowColumn j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [seedRecord, packetRecord, resetRow, seedClocks, seedLowColumn]

theorem packet_reset_low (i j : Fin 3) : seedPacketRecord (i, false) (packetLowColumn j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [seedPacketRecord, packetRecord, resetRow, packetClocks, packetLowColumn]

theorem seed_reset_clock (i j : Fin 5) :
    seedRecord (i, false) (seedClockColumn j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [seedRecord, packetRecord, resetRow, seedClocks, seedClockColumn]

theorem packet_reset_clock (i j : Fin 3) :
    seedPacketRecord (i, false) (packetClockColumn j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [seedPacketRecord, packetRecord, resetRow, packetClocks, packetClockColumn]

theorem seed_record_rank : seedRecord.rank = 10 := by
  apply paired_record_full_row_rank seedRecord seedLowColumn seedClockColumn seed_reset_low seed_reset_clock
  rw [seed_actual_determinant]
  norm_num

theorem seed_packet_record_rank : seedPacketRecord.rank = 6 := by
  apply paired_record_full_row_rank seedPacketRecord packetLowColumn packetClockColumn packet_reset_low packet_reset_clock
  rw [packet_actual_determinant]
  norm_num

theorem seed_record_surjective : Function.Surjective seedRecord.mulVec :=
  full_row_rank_surjective seedRecord seed_record_rank

theorem seed_packet_record_surjective : Function.Surjective seedPacketRecord.mulVec :=
  full_row_rank_surjective seedPacketRecord seed_packet_record_rank

end NField.ResetForests.SeedRecord
