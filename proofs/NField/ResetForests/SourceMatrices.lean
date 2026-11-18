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
/-! # Literal clock-query, curvature and sampling-defect matrices -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.QuadraticResponse

open scoped BigOperators Matrix
open MeasureTheory NField.Alignment SourceMetrics GramDecomposition
open CommonResetGram CommonResetWeightedSources CommonResetWeightedSampling
open CommonResetGeneralReciprocity CommonResetDedekind CommonResetGrid CollisionRampEnergy
open RademacherThreeTerm

def fullClockQuery (N Q : ℕ) (c : Fin N → ℝ) : ℝ :=
  4*∑ d ∈ Finset.Icc 2 N, resetWeight N (cutoffCoefficients N c) d*
    ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      weightedProfile N (cutoffCoefficients N c) ((a : ℝ)/(d : ℝ))*
        midpointRow Q ((a : ℝ)/(d : ℝ))

def clockMatrix (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => 4*((arithmeticCoefficientDedekindTerm Q (i.val+1) (j.val+1) : ℝ)+
    (arithmeticCoefficientDedekindTerm Q (j.val+1) (i.val+1) : ℝ))

def slopeSource (N : ℕ) (i : Fin N) : ℝ := ((i.val+1 : ℕ) : ℝ)

def reciprocalSource (N : ℕ) (i : Fin N) : ℝ := 1/((i.val+1 : ℕ) : ℝ)

def curvatureMatrix (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (1/(3*(Q : ℝ))) • (Matrix.vecMulVec (slopeSource N) (reciprocalSource N)+
    Matrix.vecMulVec (reciprocalSource N) (slopeSource N))

def originMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun _ _ => 1

def samplingDefectMatrix (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  continuousGram N-(1/(Q : ℝ)) • sampledGram N Q

def sourceDefect (N Q : ℕ) (c : Fin N → ℝ) : ℝ :=
  weightedDefect N Q (cutoffCoefficients N c)

theorem full_clock_query_interior (N Q : ℕ) (c : Fin N → ℝ) :
    fullClockQuery N Q c=4*weightedInterior N Q (cutoffCoefficients N c) := rfl

theorem clock_matrix_symmetric (N Q : ℕ) (i j : Fin N) :
    clockMatrix N Q i j=clockMatrix N Q j i := by
  simp only [clockMatrix, add_comm]

theorem clock_matrix_quadratic (N Q : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (clockMatrix N Q *ᵥ c)=fullClockQuery N Q c := by
  have h := weightedInterior_symmetric N Q (cutoffCoefficients N c)
  simp_rw [sum_source_indices, cutoff_coefficients_succ] at h
  rw [full_clock_query_interior, ← h]
  simp only [dotProduct, Matrix.mulVec, clockMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem curvature_matrix_entry (N Q : ℕ) (i j : Fin N) :
    curvatureMatrix N Q i j=
      ((((i.val+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)+
        (((j.val+1 : ℕ) : ℝ))/((i.val+1 : ℕ) : ℝ))/(3*(Q : ℝ)) := by
  simp only [curvatureMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.vecMulVec_apply, slopeSource, reciprocalSource]
  ring

theorem curvature_matrix_symmetric (N Q : ℕ) (i j : Fin N) :
    curvatureMatrix N Q i j=curvatureMatrix N Q j i := by
  simp only [curvature_matrix_entry, add_comm]

theorem source_slope_reading (N : ℕ) (c : Fin N → ℝ) :
    (∑ i : Fin N, c i*slopeSource N i)=slopeMoment N (cutoffCoefficients N c) := by
  rw [slopeMoment, sum_source_indices]
  simp only [cutoff_coefficients_succ, slopeSource, mul_comm]

theorem source_reciprocal_reading (N : ℕ) (c : Fin N → ℝ) :
    (∑ i : Fin N, c i*reciprocalSource N i)=
      ∑ j ∈ Finset.Icc 1 N, cutoffCoefficients N c j/(j : ℝ) := by
  rw [sum_source_indices]
  simp only [cutoff_coefficients_succ, reciprocalSource, div_eq_mul_inv, one_mul]

theorem curvature_matrix_quadratic (N Q : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (curvatureMatrix N Q *ᵥ c)=
      (2*slopeMoment N (cutoffCoefficients N c))*
        (∑ j ∈ Finset.Icc 1 N, cutoffCoefficients N c j/(j : ℝ))/(3*(Q : ℝ)) := by
  rw [← source_slope_reading, ← source_reciprocal_reading]
  calc
    _ = (1/(3*(Q : ℝ)))*
        ((∑ i : Fin N, c i*slopeSource N i)*(∑ j : Fin N, c j*reciprocalSource N j)+
          (∑ i : Fin N, c i*reciprocalSource N i)*(∑ j : Fin N, c j*slopeSource N j)) := by
      simp only [dotProduct, Matrix.mulVec, curvatureMatrix, Matrix.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.vecMulVec_apply, Finset.mul_sum,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

theorem origin_matrix_quadratic (N : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (originMatrix N *ᵥ c)=(∑ i : Fin N, c i)^2 := by
  simp only [dotProduct, Matrix.mulVec, originMatrix, one_mul, pow_two, Finset.sum_mul]

theorem origin_matrix_coherent (N : ℕ) :
    originMatrix N *ᵥ (fun _ => (1 : ℝ))=fun _ => (N : ℝ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, originMatrix]

theorem sampled_gram_coefficient {Q : ℕ} (hQ : 0 < Q) (N : ℕ) (i j : Fin N) :
    sampledGram N Q i j=
      4*(arithmeticCoefficientDedekindTerm (i.val+1) (j.val+1) Q : ℝ) := by
  rw [sampled_gram_entry]
  simp only [weighted_profile_basis]
  rw [Fin.sum_univ_eq_sum_range
    (fun a : ℕ => (2*midpointRow (i.val+1) ((a : ℝ)/(Q : ℝ)))*
      (2*midpointRow (j.val+1) ((a : ℝ)/(Q : ℝ)))) Q]
  unfold arithmeticCoefficientDedekindTerm
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [midpointRow_rational hQ, midpointRow_rational hQ]
  ring

theorem sampling_matrix_symmetric (N Q : ℕ) (i j : Fin N) :
    samplingDefectMatrix N Q i j=samplingDefectMatrix N Q j i := by
  have hG : sampledGram N Q i j=sampledGram N Q j i := by
    rw [sampled_gram_entry, sampled_gram_entry]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simp only [samplingDefectMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    continuousGram, Nat.gcd_comm, hG]
  ring

theorem sampling_matrix_quadratic (N Q : ℕ) (c : Fin N → ℝ) :
    sourceDefect N Q c=c ⬝ᵥ (samplingDefectMatrix N Q *ᵥ c) := by
  have hC := continuous_gram_quadratic N c
  simp only [star_trivial] at hC
  have hG := sampled_gram_mixed N Q c c
  simp only [← pow_two] at hG
  rw [sourceDefect, weightedDefect, ← hC]
  simp only [samplingDefectMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul]
  congr 1
  rw [hG, weightedSample, Fin.sum_univ_eq_sum_range
    (fun a : ℕ => weightedProfile N (cutoffCoefficients N c) ((a : ℝ)/(Q : ℝ))^2) Q]
  simp only [smul_eq_mul]

theorem sampling_matrix_reset_factor {p : ℕ} (hp : p.Prime) :
    samplingDefectMatrix (p-1) (p^2)=
      (1/((p^2 : ℕ) : ℝ)) •
        (originMatrix (p-1)+clockMatrix (p-1) (p^2)-curvatureMatrix (p-1) (p^2)) := by
  ext i j
  have hi : (i.val+1).Coprime (p^2) := Core.prime_cutoff_coprime hp
    (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hj : (j.val+1).Coprime (p^2) := Core.prime_cutoff_coprime hp
    (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hg : ((i.val+1).gcd (j.val+1)).gcd (p^2)=1 :=
    (hi.of_dvd_left (Nat.gcd_dvd_left _ _)).gcd_eq_one
  have h := pair_sampling_identity (Nat.succ_pos i.val) (Nat.succ_pos j.val) (pow_pos hp.pos 2)
  rw [hi.gcd_eq_one, hj.gcd_eq_one, hg] at h
  simp only [Nat.cast_one, one_pow, mul_one, Nat.succ_eq_add_one] at h
  simp only [samplingDefectMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, originMatrix, clockMatrix, curvature_matrix_entry,
    continuousGram, sampled_gram_coefficient (pow_pos hp.pos 2)]
  convert h using 1 <;> ring

theorem sampling_half_gradient_vector {p : ℕ} (hp : p.Prime) :
    samplingDefectMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))=
      fun i => (((p-1 : ℕ) : ℝ)+
        (clockMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i-
        (curvatureMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i)/((p^2 : ℕ) : ℝ) := by
  rw [sampling_matrix_reset_factor hp, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.add_mulVec, origin_matrix_coherent]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

end NField.ResetForests.QuadraticResponse
