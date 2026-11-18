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
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.Rank
/-! # The literal two-coordinate query at every packet clock -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketQueries

open scoped BigOperators Matrix

abbrev RecordIndex (t : ℕ) := Fin t × Bool

def pairQuery (t : ℕ) : Matrix (RecordIndex t) (RecordIndex t) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2 ≠ j.2 then 2 else 0

theorem record_index_card (t : ℕ) : Fintype.card (RecordIndex t) = 2 * t := by
  simp only [RecordIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

theorem pair_query_symmetric (t : ℕ) : (pairQuery t)ᵀ = pairQuery t := by
  ext i j
  simp only [Matrix.transpose_apply, pairQuery]
  have he : (i.1 = j.1 ∧ i.2 ≠ j.2) ↔ (j.1 = i.1 ∧ j.2 ≠ i.2) := by tauto
  simp only [he]

theorem pair_query_mulVec (t : ℕ) (y : RecordIndex t → ℝ) (i : Fin t) (b : Bool) :
    (pairQuery t *ᵥ y) (i, b) = 2 * y (i, !b) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp [pairQuery]
  · intro j _ hji
    simp [pairQuery, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem pair_query_quadratic (t : ℕ) (y : RecordIndex t → ℝ) :
    y ⬝ᵥ (pairQuery t *ᵥ y) = 4 * ∑ i : Fin t, y (i, false) * y (i, true) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, pair_query_mulVec,
    Bool.not_false, Bool.not_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pair_query_inverse_product (t : ℕ) :
    pairQuery t * ((1 / 4 : ℝ) • pairQuery t) = 1 := by
  apply Matrix.mulVec_injective
  funext y
  ext ⟨i, b⟩
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  simp only [pair_query_mulVec, Pi.smul_apply, smul_eq_mul, Bool.not_not, Matrix.one_mulVec]
  ring

theorem pair_query_rank (t : ℕ) : (pairQuery t).rank = 2 * t := by
  have h := Matrix.rank_mul_le_left (pairQuery t) ((1 / 4 : ℝ) • pairQuery t)
  rw [pair_query_inverse_product, Matrix.rank_one, record_index_card] at h
  exact le_antisymm ((Matrix.rank_le_card_width _).trans_eq (record_index_card t)) h

end NField.ResetForests.PacketQueries
