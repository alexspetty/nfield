/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.ResetForests.DivisorBudget
import NField.ResetForests.Sampling
import NField.ResetForests.OrderedWork
import NField.ResetForests.Words
import NField.ResetForests.Carry
import NField.ResetForests.Readout
import NField.ResetForests.CoherentWork
import NField.ResetForests.Targets
import NField.ResetForests.GridWork
import NField.ResetForests.Centered
import NField.ResetForests.CarryClock
import NField.ResetForests.ClockBinary
import NField.ResetForests.PhaseFringe
import NField.ResetForests.LoadTail
import NField.ResetForests.ForestRates
import NField.ResetForests.Opening
import NField.ResetForests.Complement
import NField.ResetForests.WindowExample
import NField.ResetForests.EnergyMatrices
import NField.ResetForests.FibreDirections
import NField.ResetForests.FibreBasisTrace
import NField.ResetForests.GramSectors
import NField.ResetForests.TorusIncidence
import NField.ResetForests.CompleteReset
import NField.ResetForests.OrderedMasks
import NField.ResetForests.PacketPopulation
import NField.ResetForests.PacketReading
import NField.ResetForests.PacketPeriod
import NField.ResetForests.StripTransport
import NField.ResetForests.RecordSignature
import NField.ResetForests.ActualRecord
/-! # Exact rational data for the complete thirty-harmonic seed record -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.SeedRecord

open scoped BigOperators Matrix
open NField.Alignment CollisionRampEnergy CommonResetGrid DedekindReciprocity PacketQueries

def rationalDetector (Q k j : ℕ) : ℚ :=
  2 * ∑ a ∈ BranchTransport.unitAddresses k, rationalSawtooth (j * a) k * rationalSawtooth (Q * a) k

def seedClocks : Fin 5 → ℕ := ![23, 22, 19, 24, 20]
def packetClocks : Fin 3 → ℕ := ![23, 22, 19]
def fringeClocks : Fin 2 → ℕ := ![24, 20]

def seedRecord : Matrix (RecordIndex 5) (Fin 30) ℝ := packetRecord 30 961 seedClocks
def seedPacketRecord : Matrix (RecordIndex 3) (Fin 30) ℝ := packetRecord 30 961 packetClocks
def seedFringeRecord : Matrix (RecordIndex 2) (Fin 30) ℝ := packetRecord 30 961 fringeClocks

def seedDetectorTable : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-7/23, -7/23, 17/23, 1/23, -77/23;
      4/11, -2/11, 8/11, -10/11, 4/11;
      3/19, -11/19, 21/19, -21/19, -9/19;
      49/36, 13/18, 1/4, 4/9, 41/36;
      7/5, 4/5, 1, 2/5, 0]

def seedPacketMinor : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-7/23, -7/23, 17/23;
      4/11, -2/11, 8/11;
      3/19, -11/19, 21/19]

theorem detector_row_rational {N Q k : ℕ} (hk : 0 < k) (j : Fin N) :
    detectorRow N Q k j = (rationalDetector Q k (j.val + 1) : ℝ) := by
  unfold detectorRow rationalDetector
  simp_rw [midpointRow_rational hk]
  push_cast
  rfl

theorem seed_row23 : (fun j : Fin 5 => rationalDetector 961 23 (j.val + 1)) =
    ![-7/23, -7/23, 17/23, 1/23, -77/23] := by
  ext j
  fin_cases j <;>
    norm_num [rationalDetector, BranchTransport.unitAddresses,
      Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_row22 : (fun j : Fin 5 => rationalDetector 961 22 (j.val + 1)) =
    ![4/11, -2/11, 8/11, -10/11, 4/11] := by
  ext j
  fin_cases j <;>
    norm_num [rationalDetector, BranchTransport.unitAddresses,
      Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_row19 : (fun j : Fin 5 => rationalDetector 961 19 (j.val + 1)) =
    ![3/19, -11/19, 21/19, -21/19, -9/19] := by
  ext j
  fin_cases j <;>
    norm_num [rationalDetector, BranchTransport.unitAddresses,
      Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_row24 : (fun j : Fin 5 => rationalDetector 961 24 (j.val + 1)) =
    ![49/36, 13/18, 1/4, 4/9, 41/36] := by
  ext j
  fin_cases j <;>
    norm_num [rationalDetector, BranchTransport.unitAddresses,
      Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_row20 : (fun j : Fin 5 => rationalDetector 961 20 (j.val + 1)) =
    ![7/5, 4/5, 1, 2/5, 0] := by
  ext j
  fin_cases j <;>
    norm_num [rationalDetector, BranchTransport.unitAddresses,
      Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_table_exact :
    (fun i j => rationalDetector 961 (seedClocks i) (j.val + 1)) = seedDetectorTable := by
  ext i j
  fin_cases i
  · exact congrFun seed_row23 j
  · exact congrFun seed_row22 j
  · exact congrFun seed_row19 j
  · exact congrFun seed_row24 j
  · exact congrFun seed_row20 j

theorem seed_packet_minor_exact :
    (fun i j => rationalDetector 961 (packetClocks i) (j.val + 1)) = seedPacketMinor := by
  ext i j
  have he := congrFun (congrFun seed_table_exact (⟨i.val, by omega⟩ : Fin 5))
    (⟨j.val, by omega⟩ : Fin 5)
  fin_cases i <;> fin_cases j <;> exact he

theorem seed_detector_determinant : seedDetectorTable.det = (-88076/216315 : ℚ) := by
  norm_num [seedDetectorTable, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.det_fin_two, Matrix.submatrix, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  norm_num [Fin.lt_def, Fin.le_def, Fin.ext_iff, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem seed_packet_determinant : seedPacketMinor.det = (-548/4807 : ℚ) := by
  norm_num [seedPacketMinor, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end NField.ResetForests.SeedRecord
