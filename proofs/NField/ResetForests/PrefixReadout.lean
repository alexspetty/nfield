/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixWork
import NField.ResetForests.Readout
/-! # The full final detector and the prefix mixed-Gram formulas -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def finalReadout (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun c := b ⬝ᵥ (A *ᵥ c)
  map_add' x y := by simp only [Matrix.mulVec_add, dotProduct_add]
  map_smul' a x := by simp only [Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply]

omit [DecidableEq ι] in
theorem final_readout_covector (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (c : Fin N → ℝ) :
    finalReadout A b c = (Aᵀ *ᵥ b) ⬝ᵥ c := transpose_pairing A b c

def readoutSource (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix ι (Fin N) ℝ)
    (b : ι → ℝ) : Fin N → ℝ := G⁻¹ *ᵥ (Aᵀ *ᵥ b)

omit [DecidableEq ι] in
theorem readout_source_mem (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix ι (Fin N) ℝ)
    (b : ι → ℝ) : readoutSource G A b ∈ dualSpan G A := by
  refine ⟨b, ?_⟩
  change (G⁻¹ * Aᵀ) *ᵥ b = G⁻¹ *ᵥ (Aᵀ *ᵥ b)
  exact (Matrix.mulVec_mulVec _ _ _).symm

omit [DecidableEq ι] in
theorem readout_source_pairing (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (c : Fin N → ℝ) :
    sourceWork G (readoutSource G A b) c = finalReadout A b c := by
  rw [work_symm G hG.1]
  unfold sourceWork readoutSource
  rw [Matrix.mulVec_mulVec, metric_inverse_right G hG, Matrix.one_mulVec,
    dotProduct_comm, ← final_readout_covector]

omit [DecidableEq ι] in
theorem readout_source_energy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) :
    sourceWork G (readoutSource G A b) (readoutSource G A b) =
      (Aᵀ *ᵥ b) ⬝ᵥ (G⁻¹ *ᵥ (Aᵀ *ᵥ b)) := by
  rw [readout_source_pairing G hG A b _, final_readout_covector]
  rfl

theorem prefix_readout_sum (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (h0 : J 0 = ∅)
    (c : Fin N → ℝ) (L : ℕ) (hL : J L = Finset.univ) :
    finalReadout A b c = ∑ r ∈ Finset.range L, finalReadout A b (prefixIncrement G hG A J c r) := by
  rw [← map_sum, prefix_increment_sum G hG A J h0 c L]
  change b ⬝ᵥ (A *ᵥ c) = b ⬝ᵥ (A *ᵥ oldSource G hG (restrictedRecord A (J L)) c)
  rw [hL, restricted_univ, old_source_reading]

def prefixCost (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (c : Fin N → ℝ) (L : ℕ) : ℝ :=
  Core.readoutCost (Finset.range L)
    (fun r => sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r))
    (fun r => finalReadout A b (prefixIncrement G hG A J c r))

theorem zero_increment_readout (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (c : Fin N → ℝ) (r : ℕ)
    (he : sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) = 0) :
    prefixIncrement G hG A J c r = 0 ∧ finalReadout A b (prefixIncrement G hG A J c r) = 0 := by
  have hv := (source_work_zero_iff G hG _).mp he
  exact ⟨hv, by rw [hv, map_zero]⟩

theorem prefix_cost_positive_terms (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (c : Fin N → ℝ) (L : ℕ) :
    prefixCost G hG A b J c L =
      ∑ r ∈ (Finset.range L).filter (fun r =>
        0 < sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r)),
        (finalReadout A b (prefixIncrement G hG A J c r)) ^ 2 /
          sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) := by
  unfold prefixCost Core.readoutCost
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with hr
  · rfl
  · have he : sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) = 0 :=
      le_antisymm (le_of_not_gt hr) (source_work_nonnegative G hG _)
    simp only [he, div_zero]

theorem prefix_signed_bound (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (hJ : Monotone J) (h0 : J 0 = ∅) (c : Fin N → ℝ) (L : ℕ)
    (hL : J L = Finset.univ) :
    |finalReadout A b c| ^ 2 ≤
      (∑ r ∈ Finset.range L, sourceWork G (prefixIncrement G hG A J c r)
        (prefixIncrement G hG A J c r)) * prefixCost G hG A b J c L ∧
    (∑ r ∈ Finset.range L, sourceWork G (prefixIncrement G hG A J c r)
        (prefixIncrement G hG A J c r)) * prefixCost G hG A b J c L ≤
      sourceWork G c c * prefixCost G hG A b J c L := by
  have he (r : ℕ) (_ : r ∈ Finset.range L) :=
    source_work_nonnegative G hG (prefixIncrement G hG A J c r)
  have hz (r : ℕ) (_ : r ∈ Finset.range L)
      (hr : sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) = 0) :=
    (zero_increment_readout G hG A b J c r hr).2
  constructor
  · rw [sq_abs, prefix_readout_sum G hG A b J h0 c L hL]
    exact Core.signed_readout_bound _ _ _ he hz
  · apply mul_le_mul_of_nonneg_right _ (Core.readout_cost_nonneg _ _ _ he)
    have hE := prefix_complete_source_energy G hG A J hJ h0 c L
    have hn := source_work_nonnegative G hG (c - prefixSource G hG A J c L)
    linarith

def mixedRecordGram (G : Matrix (Fin N) (Fin N) ℝ)
    (A B : Matrix ι (Fin N) ℝ) : Matrix ι ι ℝ := A * G⁻¹ * Bᵀ

theorem full_future_readings (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    A *ᵥ prefixSource G hG A J c r =
      mixedRecordGram G A (restrictedRecord A (J r)) *ᵥ
        (recordInverse G hG (restrictedRecord A (J r)) *ᵥ (restrictedRecord A (J r) *ᵥ c)) := by
  simp only [prefixSource, oldSource, liftMatrix, mixedRecordGram,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem prefix_detector_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    finalReadout A b (prefixSource G hG A J c r) =
      b ⬝ᵥ (mixedRecordGram G A (restrictedRecord A (J r)) *ᵥ
        (recordInverse G hG (restrictedRecord A (J r)) *ᵥ (restrictedRecord A (J r) *ᵥ c))) :=
  congrArg (fun y => b ⬝ᵥ y) (full_future_readings G hG A J c r)

theorem prefix_increment_cost_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (L : ℕ) :
    prefixCost G hG A b J c L =
      ∑ r ∈ Finset.range L,
        (finalReadout A b (prefixSource G hG A J c (r + 1)) -
          finalReadout A b (prefixSource G hG A J c r)) ^ 2 /
        (sourceWork G (prefixSource G hG A J c (r + 1)) (prefixSource G hG A J c (r + 1)) -
          sourceWork G (prefixSource G hG A J c r) (prefixSource G hG A J c r)) := by
  unfold prefixCost Core.readoutCost
  apply Finset.sum_congr rfl
  intro r _
  dsimp only
  rw [prefix_increment_energy G hG A J hJ c r]
  simp only [prefixIncrement, map_sub]

end NField.ResetForests.PrefixGeometry
