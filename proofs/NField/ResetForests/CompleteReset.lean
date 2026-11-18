/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.QuadraticDerivative
import NField.Alignment.CommonResetAllGrids
/-! # All three assertions of the complete reset identity -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.QuadraticResponse

open scoped BigOperators Matrix
open NField.Alignment SourceMetrics GramDecomposition
open CommonResetGram CommonResetWeightedSources CommonResetWeightedSampling
open CommonResetAllGrids CommonResetSampling CollisionRampEnergy

theorem full_source_reset_identity {p : ℕ} (hp : p.Prime) (c : Fin (p-1) → ℝ) :
    sourceDefect (p-1) (p^2) c=
      ((∑ i : Fin (p-1), c i)^2+fullClockQuery (p-1) (p^2) c-
        (2*slopeMoment (p-1) (cutoffCoefficients (p-1) c))*
          (∑ j ∈ Finset.Icc 1 (p-1), cutoffCoefficients (p-1) c j/(j : ℝ))/
            (3*((p^2 : ℕ) : ℝ)))/((p^2 : ℕ) : ℝ) := by
  rw [sampling_matrix_quadratic, sampling_matrix_reset_factor hp,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_smul, dotProduct_sub, dotProduct_add,
    origin_matrix_quadratic, clock_matrix_quadratic, curvature_matrix_quadratic]
  simp only [smul_eq_mul]
  ring

theorem cutoff_reset_weight_coherent (N d : ℕ) :
    resetWeight N (cutoffCoefficients N (fun _ => 1)) d=((N/d : ℕ) : ℝ) := by
  have he : resetWeight N (cutoffCoefficients N (fun _ => 1)) d=
      resetWeight N (fun _ => 1) d := by
    unfold resetWeight
    apply Finset.sum_congr rfl
    intro j hj
    simp only [cutoffCoefficients, dif_pos hj]
  rw [he, resetWeight_one]

def coherentClockContribution (N Q k : ℕ) : ℝ :=
  4*((N/k : ℕ) : ℝ)*
    ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
      weightedProfile N (fun _ => 1) ((a : ℝ)/(k : ℝ))*
        midpointRow Q ((a : ℝ)/(k : ℝ))

theorem full_clock_query_coherent (N Q : ℕ) :
    fullClockQuery N Q (fun _ => 1)=
      ∑ k ∈ Finset.Icc 2 N, coherentClockContribution N Q k := by
  simp only [fullClockQuery, coherentClockContribution, Finset.mul_sum,
    cutoff_reset_weight_coherent, cutoff_complete_profile]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem coherent_query_interior (N Q : ℕ) :
    (∑ k ∈ Finset.Icc 2 N, coherentClockContribution N Q k)=4*interiorSource N Q := by
  simp only [coherentClockContribution, interiorSource, unit_weights, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem coherent_defect_literal (N Q : ℕ) :
    sourceDefect N Q (fun _ => 1)=defect N Q := by
  simp only [sourceDefect, weightedDefect, weightedSample, cutoff_complete_profile,
    unit_weights, defect, continuousEnergy, sampledEnergy]

theorem coherent_complete_reset_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    sourceDefect (p-1) (p^2) (fun _ => 1)=
      ((((p-1 : ℕ) : ℝ)^2+
        ∑ k ∈ Finset.Icc 2 (p-1), coherentClockContribution (p-1) (p^2) k)/(p : ℝ)^2)-
        ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) := by
  rw [coherent_defect_literal, prime_square_sampling_identity hp hodd, coherent_query_interior]
  ring

theorem full_sampling_half_gradient_coordinate {p : ℕ} (hp : p.Prime) (i : Fin (p-1)) :
    (1/2 : ℝ)*
      (fderiv ℝ (sourceDefect (p-1) (p^2)) (fun _ => (1 : ℝ))) (Pi.single i 1)=
      (((p-1 : ℕ) : ℝ)+
        (clockMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i-
        (curvatureMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i)/((p^2 : ℕ) : ℝ) := by
  rw [full_sampling_fderiv hp]
  simp only [smul_apply, source_covector_apply, dotProduct_single, mul_one, smul_eq_mul]
  ring

end NField.ResetForests.QuadraticResponse
