/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixCoarsening
import NField.ResetForests.PacketPrefixes
import NField.ResetForests.CompleteReset
import NField.ResetForests.CompressedPrefix
/-! # The coherent work theorem for actual ordered packet populations -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry
open NField.Alignment CollisionRampEnergy CommonResetWeightedSources CommonResetGram

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prefix_covector_cost (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (L : ℕ) :
    let v := prefixIncrement G hG A J c
    let g := readoutSource G A b
    let z := metricReadoutProjection G (Finset.range L) v (finalReadout A b)
    IsMetricProjection G (positiveDirectionSpan G (Finset.range L) v) g z ∧
    sourceWork G z z = prefixCost G hG A b J c L ∧
    prefixCost G hG A b J c L ≤ (Aᵀ *ᵥ b) ⬝ᵥ (G⁻¹ *ᵥ (Aᵀ *ᵥ b)) := by
  dsimp only
  have ho : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L, i ≠ j →
      sourceWork G (prefixIncrement G hG A J c i) (prefixIncrement G hG A J c j) = 0 :=
    fun i _ j _ hij => prefix_increments_orthogonal G hG A J hJ c hij
  refine ⟨readout_is_metric_projection G hG _ _ _ ho (readoutSource G A b)
    (readout_source_pairing G hG A b), readout_projection_energy G hG _ _ _ ho, ?_⟩
  rw [← readout_source_energy G hG A b]
  exact readout_projection_norm_bound G hG _ _ _ ho (readoutSource G A b)
    (readout_source_pairing G hG A b)

theorem physical_native_readout (p : ℕ) (loads : Finset ℕ) (c : Fin (p - 1) → ℝ) :
    finalReadout (physicalRecord p loads) (physicalReadoutWeights p loads) c =
      4 * ∑ k ∈ chosenClocks p loads, ((p - 1) / k : ℕ) *
        ∑ a ∈ BranchTransport.unitAddresses k,
          weightedProfile (p - 1) (SourceMetrics.cutoffCoefficients (p - 1) c) ((a : ℝ) / (k : ℝ)) *
            midpointRow (p ^ 2) ((a : ℝ) / (k : ℝ)) := by
  rw [physical_linear_readout, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [PacketQueries.detector_row_reading]
  exact mul_assoc _ _ _

theorem physical_fixed_reset_populations (p : ℕ) (loads : Finset ℕ) :
    physicalReadoutWeights p loads = fun i =>
      if i.2 then 4 * resetWeight (p - 1) (SourceMetrics.cutoffCoefficients (p - 1) (fun _ => 1)) i.1.val
      else 0 := by
  funext i
  simp only [physicalReadoutWeights, QuadraticResponse.cutoff_reset_weight_coherent]

/-- Every hypothesis describes the prime and the chosen fixed prefix cuts.
The physical rows, source metric, projections and orthogonal increments
are constructed from those data. No cancellation estimate is assumed. -/
theorem actual_source_coherent_work {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (hc : Monotone cuts) (h0 : cuts 0 = 0)
    (L : ℕ) (hL : cuts L = (orderedPackets p loads).length) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := physicalRecord p loads
    let b := physicalReadoutWeights p loads
    let J := physicalPrefixes p loads cuts
    let c : Fin (p - 1) → ℝ := fun _ => 1
    let v := prefixIncrement G hG A J c
    let e := fun r => sourceWork G (v r) (v r)
    let R := prefixCost G hG A b J c L
    let g := readoutSource G A b
    let z := metricReadoutProjection G (Finset.range L) v (finalReadout A b)
    (∀ i j, i ≠ j → sourceWork G (v i) (v j) = 0) ∧
    (∑ r ∈ Finset.range L, e r) +
      sourceWork G (c - prefixSource G hG A J c L) (c - prefixSource G hG A J c L) =
        sourceWork G c c ∧
    |finalReadout A b c| ^ 2 ≤ (∑ r ∈ Finset.range L, e r) * R ∧
    (∑ r ∈ Finset.range L, e r) * R ≤ sourceWork G c c * R ∧
    IsMetricProjection G (positiveDirectionSpan G (Finset.range L) v) g z ∧
    sourceWork G z z = R ∧ R ≤ (Aᵀ *ᵥ b) ⬝ᵥ (G⁻¹ *ᵥ (Aᵀ *ᵥ b)) := by
  dsimp only
  have hJ := physical_prefix_monotone p loads cuts hc
  have hJ0 := physical_prefix_zero p loads cuts h0
  have hJL := physical_prefix_final p loads cuts L hL
  let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
  have hG : G.PosDef := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
  have hb := prefix_signed_bound G hG (physicalRecord p loads) (physicalReadoutWeights p loads)
    (physicalPrefixes p loads cuts) hJ hJ0 (fun _ => 1) L hJL
  have hpj := prefix_covector_cost G hG (physicalRecord p loads) (physicalReadoutWeights p loads)
    (physicalPrefixes p loads cuts) hJ (fun _ => 1) L
  exact ⟨(fun i j hij => prefix_increments_orthogonal _ _ _ _ hJ _ hij),
    prefix_complete_source_energy _ _ _ _ hJ hJ0 _ L, hb.1, hb.2, hpj.1, hpj.2.1, hpj.2.2⟩

theorem actual_prefix_coarsening {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (hc : Monotone cuts) (L : ℕ)
    (groups : Finset (Finset ℕ))
    (hdisj : (groups : Set (Finset ℕ)).PairwiseDisjoint id)
    (hcover : groups.biUnion id = Finset.range L) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := physicalRecord p loads
    let b := physicalReadoutWeights p loads
    let J := physicalPrefixes p loads cuts
    let v := prefixIncrement G hG A J (fun _ => 1)
    (∑ B ∈ groups, (finalReadout A b (∑ r ∈ B, v r)) ^ 2 /
      sourceWork G (∑ r ∈ B, v r) (∑ r ∈ B, v r)) ≤
        prefixCost G hG A b J (fun _ => 1) L := by
  dsimp only
  exact prefix_coarsening_cost_le _ _ _ _ _ (physical_prefix_monotone p loads cuts hc)
    _ L groups hdisj hcover

theorem actual_prefix_energy_formula {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (r : ℕ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := physicalRecord p loads
    let J := physicalPrefixes p loads cuts
    let A_J := restrictedRecord A (J r)
    let y_J := A_J *ᵥ (fun _ => 1)
    sourceWork G (prefixSource G hG A J (fun _ => 1) r) (prefixSource G hG A J (fun _ => 1) r) =
      y_J ⬝ᵥ (recordInverse G hG A_J *ᵥ y_J) := by
  dsimp only
  exact prefix_work_formula _ _ _ _ _ r

theorem actual_prefix_full_detector_formula {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (r : ℕ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := physicalRecord p loads
    let b := physicalReadoutWeights p loads
    let J := physicalPrefixes p loads cuts
    let A_J := restrictedRecord A (J r)
    let y_J := A_J *ᵥ (fun _ => 1)
    finalReadout A b (prefixSource G hG A J (fun _ => 1) r) =
      b ⬝ᵥ (mixedRecordGram G A A_J *ᵥ (recordInverse G hG A_J *ᵥ y_J)) := by
  dsimp only
  exact prefix_detector_formula _ _ _ _ _ _ r

theorem prefix_source_is_projection (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    IsMetricProjection G (dualSpan G (restrictedRecord A (J r))) c (prefixSource G hG A J c r) := by
  refine ⟨projected_source_mem G hG _ c, ?_⟩
  intro w hw
  exact dual_span_kernel_work G hG _ w _ hw (projected_source_kernel G hG _ c)

theorem prefix_cost_metric_norm (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (L : ℕ) :
    let z := metricReadoutProjection G (Finset.range L) (prefixIncrement G hG A J c) (finalReadout A b)
    (@norm (Fin N → ℝ) (G.toNormedAddCommGroup hG).toSeminormedAddCommGroup.toNorm z) ^ 2 =
      prefixCost G hG A b J c L := by
  dsimp only
  rw [source_metric_norm_sq]
  exact (prefix_covector_cost G hG A b J hJ c L).2.1

theorem actual_compressed_cost_formula {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (hc : Monotone cuts) (L : ℕ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := physicalRecord p loads
    let b := physicalReadoutWeights p loads
    let J := physicalPrefixes p loads cuts
    prefixCost G hG A b J (fun _ => 1) L =
      ∑ r ∈ Finset.range L,
        (compressedPrediction G hG A b J (fun _ => 1) (r + 1) -
          compressedPrediction G hG A b J (fun _ => 1) r) ^ 2 /
        (compressedEnergy G hG A J (fun _ => 1) (r + 1) -
          compressedEnergy G hG A J (fun _ => 1) r) := by
  dsimp only
  exact compressed_increment_cost_formula _ _ _ _ _ (physical_prefix_monotone p loads cuts hc) _ L

end NField.ResetForests.PrefixGeometry
