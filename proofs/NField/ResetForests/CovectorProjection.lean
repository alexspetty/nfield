/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixReadout
/-! # Positive source directions and the actual metric projection of a covector -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry

variable {N : ℕ} {κ : Type*}

theorem work_smul_left (G : Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (x y : Fin N → ℝ) :
    sourceWork G (a • x) y = a * sourceWork G x y := by
  simp only [sourceWork, smul_dotProduct, smul_eq_mul]

theorem work_smul_right (G : Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (x y : Fin N → ℝ) :
    sourceWork G x (a • y) = a * sourceWork G x y := by
  simp only [sourceWork, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

def positiveDirectionSpan (G : Matrix (Fin N) (Fin N) ℝ) (s : Finset κ)
    (v : κ → Fin N → ℝ) : Submodule ℝ (Fin N → ℝ) :=
  Submodule.span ℝ {x | ∃ i ∈ s, 0 < sourceWork G (v i) (v i) ∧ x = v i}

def metricReadoutProjection (G : Matrix (Fin N) (Fin N) ℝ) (s : Finset κ)
    (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ) : Fin N → ℝ :=
  ∑ i ∈ s, (f (v i) / sourceWork G (v i) (v i)) • v i

def IsMetricProjection (G : Matrix (Fin N) (Fin N) ℝ)
    (Z : Submodule ℝ (Fin N → ℝ)) (x z : Fin N → ℝ) : Prop :=
  z ∈ Z ∧ ∀ w ∈ Z, sourceWork G w (x - z) = 0

theorem readout_projection_mem (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ) :
    metricReadoutProjection G s v f ∈ positiveDirectionSpan G s v := by
  unfold metricReadoutProjection
  apply Submodule.sum_mem
  intro i hi
  by_cases he : 0 < sourceWork G (v i) (v i)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, he, rfl⟩)
  · have hz : sourceWork G (v i) (v i) = 0 :=
      le_antisymm (le_of_not_gt he) (source_work_nonnegative G hG _)
    have hv := (source_work_zero_iff G hG _).mp hz
    rw [hv, smul_zero]
    exact Submodule.zero_mem _

theorem readout_projection_direction (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0)
    {i : κ} (hi : i ∈ s) :
    sourceWork G (metricReadoutProjection G s v f) (v i) = f (v i) := by
  classical
  unfold metricReadoutProjection
  rw [work_sum_left]
  simp only [work_smul_left]
  rw [Finset.sum_eq_single i]
  · by_cases he : sourceWork G (v i) (v i) = 0
    · have hv := (source_work_zero_iff G hG _).mp he
      rw [he, div_zero, zero_mul, hv, map_zero]
    · exact div_mul_cancel₀ _ he
  · intro j hj hji
    rw [ho j hj i hi hji, mul_zero]
  · exact fun h => (h hi).elim

theorem readout_projection_energy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0) :
    sourceWork G (metricReadoutProjection G s v f) (metricReadoutProjection G s v f) =
      Core.readoutCost s (fun i => sourceWork G (v i) (v i)) (fun i => f (v i)) := by
  change sourceWork G (∑ i ∈ s, (f (v i) / sourceWork G (v i) (v i)) • v i)
    (metricReadoutProjection G s v f) = _
  rw [work_sum_left]
  unfold Core.readoutCost
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [work_smul_left, work_symm G hG.1 (v i) (metricReadoutProjection G s v f),
    readout_projection_direction G hG s v f ho hi]
  ring

theorem readout_projection_residual (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0)
    (g : Fin N → ℝ) (hg : ∀ x, sourceWork G g x = f x) :
    ∀ w ∈ positiveDirectionSpan G s v,
      sourceWork G w (g - metricReadoutProjection G s v f) = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, hi, _, rfl⟩ := hw
    rw [work_sub_right, work_symm G hG.1 (v i) g, hg,
      work_symm G hG.1 (v i) (metricReadoutProjection G s v f),
      readout_projection_direction G hG s v f ho hi, sub_self]
  | zero => simp only [sourceWork, zero_dotProduct]
  | add x y _ _ hx hy =>
    change sourceWork G (x + y) _ = 0
    simp only [sourceWork, add_dotProduct] at hx hy ⊢
    rw [hx, hy, add_zero]
  | smul a x _ hx => rw [work_smul_left, hx, mul_zero]

theorem readout_is_metric_projection (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0)
    (g : Fin N → ℝ) (hg : ∀ x, sourceWork G g x = f x) :
    IsMetricProjection G (positiveDirectionSpan G s v) g (metricReadoutProjection G s v f) :=
  ⟨readout_projection_mem G hG s v f, readout_projection_residual G hG s v f ho g hg⟩

theorem metric_projection_unique (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (Z : Submodule ℝ (Fin N → ℝ)) (g x y : Fin N → ℝ)
    (hx : IsMetricProjection G Z g x) (hy : IsMetricProjection G Z g y) : x = y := by
  have hd : x - y ∈ Z := Z.sub_mem hx.1 hy.1
  have h1 := hx.2 (x - y) hd
  have h2 := hy.2 (x - y) hd
  have he : sourceWork G (x - y) (x - y) = 0 := by
    rw [work_sub_right] at h1 h2 ⊢
    linarith
  exact sub_eq_zero.mp ((source_work_zero_iff G hG _).mp he)

theorem readout_projection_norm_bound (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset κ) (v : κ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0)
    (g : Fin N → ℝ) (hg : ∀ x, sourceWork G g x = f x) :
    Core.readoutCost s (fun i => sourceWork G (v i) (v i)) (fun i => f (v i)) ≤
      sourceWork G g g := by
  let z := metricReadoutProjection G s v f
  have hz := readout_projection_residual G hG s v f ho g hg z (readout_projection_mem G hG s v f)
  have he := PacketQueries.symmetric_query_add G (hermitian_transpose G hG.1) z (g - z)
  have hs : z + (g - z) = g := by abel
  rw [hs] at he
  change sourceWork G g g = sourceWork G z z + sourceWork G (g - z) (g - z) +
    2 * sourceWork G z (g - z) at he
  have hp := readout_projection_energy G hG s v f ho
  have hn := source_work_nonnegative G hG (g - z)
  change sourceWork G z z = _ at hp
  linarith

end NField.ResetForests.PrefixGeometry
