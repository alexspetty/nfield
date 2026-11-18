/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestSelection
/-! # Both actual work forms and their full covectors in the integral chart -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ResetMasks

open scoped BigOperators Matrix
open MeasureTheory Module NField.Alignment CommonResetGram SourceMetrics FibreReconstruction GramDecomposition

theorem forest_basis_column (R : Type*) [CommRing R] (N Ω : ℕ) (j : Fin N) :
    forestBasis R N Ω j=fun i => forestMatrix R N Ω i j := by
  simp only [forestBasis, Basis.map_apply, Pi.basisFun_apply]
  change forestMatrix R N Ω *ᵥ Pi.single j 1=_
  rw [Matrix.mulVec_single_one]
  rfl

theorem forest_basis_repr (R : Type*) [CommRing R] (N Ω : ℕ) (c : Fin N → R) (j : Fin N) :
    (forestBasis R N Ω).repr c j=(forestInverse R N Ω *ᵥ c) j := by
  change (Pi.basisFun R (Fin N)).repr ((forestEquiv R N Ω).symm c) j=_
  rw [Pi.basisFun_repr]
  rfl

theorem coherent_basis_coordinates (N Ω : ℕ) (j : Fin N) :
    (forestBasis ℝ N Ω).repr (fun _ => 1) j=
      if j.val+1 ∣ Ω then (forestPopulation N Ω j : ℝ) else 1 := by
  rw [forest_basis_repr]
  exact forest_coherent_population N Ω j

theorem forest_matrix_inside_column (R : Type*) [CommRing R] {N Ω : ℕ}
    (j : Fin N) (hj : j.val+1 ∣ Ω) (i : Fin N) :
    forestMatrix R N Ω i j=if i=j then 1 else 0 := by
  by_cases hij : i=j <;> simp [forestMatrix, forestTransfer, hj, hij]

theorem forest_matrix_outside_row (R : Type*) [CommRing R] {N Ω : ℕ}
    (i : Fin N) (hi : ¬i.val+1 ∣ Ω) (j : Fin N) :
    forestMatrix R N Ω i j=if i=j then 1 else 0 := by
  have hne : i ≠ forestRoot N Ω j := by
    intro he
    have h := forest_root_divides N Ω j
    rw [← he] at h
    exact hi h
  have hT : forestTransfer R N Ω i j=0 := by
    simp only [forestTransfer, hne, if_false]
    split_ifs <;> rfl
  rw [forestMatrix, Matrix.sub_apply, hT, sub_zero]
  exact Matrix.one_apply

theorem forest_matrix_inside_outside (R : Type*) [CommRing R] {N Ω : ℕ}
    (i j : Fin N) (hi : i.val+1 ∣ Ω) (hj : ¬j.val+1 ∣ Ω) :
    forestMatrix R N Ω i j= -(if i=forestRoot N Ω j then 1 else 0) := by
  have hij : i ≠ j := by
    intro he
    rw [he] at hi
    exact hj hi
  simp [forestMatrix, forestTransfer, hj, hij]

def forestGram (N Ω : ℕ) (W : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (forestMatrix ℝ N Ω)ᵀ*W*forestMatrix ℝ N Ω

theorem forest_gram_mixed (N Ω : ℕ) (W : Matrix (Fin N) (Fin N) ℝ) (ξ η : Fin N → ℝ) :
    (forestMatrix ℝ N Ω *ᵥ ξ) ⬝ᵥ (W *ᵥ (forestMatrix ℝ N Ω *ᵥ η))=
      ξ ⬝ᵥ (forestGram N Ω W *ᵥ η) := by
  rw [forestGram, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem forest_gram_symmetric (N Ω : ℕ) (W : Matrix (Fin N) (Fin N) ℝ)
    (hW : ∀ i j, W i j=W j i) : ∀ i j, forestGram N Ω W i j=forestGram N Ω W j i := by
  have hWT : Wᵀ=W := by ext i j; exact hW j i
  have hG : (forestGram N Ω W)ᵀ=forestGram N Ω W := by
    simp only [forestGram, Matrix.transpose_mul, Matrix.transpose_transpose, hWT,
      Matrix.mul_assoc]
  intro i j
  exact congrArg (fun A => A j i) hG

theorem forest_gram_entry (N Ω : ℕ) (W : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    forestGram N Ω W i j=
      (forestBasis ℝ N Ω i) ⬝ᵥ (W *ᵥ forestBasis ℝ N Ω j) := by
  have h := forest_gram_mixed N Ω W (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul] at h
  simpa only [forest_basis_column, Matrix.col_apply'] using h.symm

theorem forest_root_outside_cross {N Ω : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (hi : i.val+1 ∣ Ω) (hj : ¬j.val+1 ∣ Ω) :
    forestGram N Ω W i j=W i j-W i (forestRoot N Ω j) := by
  rw [forest_gram_entry, forest_basis_apply, forest_basis_apply, if_pos hi, if_neg hj,
    Matrix.mulVec_sub, dotProduct_sub]
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul,
    Matrix.col, Matrix.transpose_apply]

theorem forest_outside_block {N Ω : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (hi : ¬i.val+1 ∣ Ω) (hj : ¬j.val+1 ∣ Ω) :
    forestGram N Ω W i j=W i j-W i (forestRoot N Ω j)-W (forestRoot N Ω i) j+
      W (forestRoot N Ω i) (forestRoot N Ω j) := by
  rw [forest_gram_entry, forest_basis_apply, forest_basis_apply, if_neg hi, if_neg hj,
    Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul,
    Matrix.col, Matrix.transpose_apply]
  ring

theorem forest_gram_hasFDerivAt (N Ω : ℕ) (W : Matrix (Fin N) (Fin N) ℝ)
    (hW : ∀ i j, W i j=W j i) (ξ : Fin N → ℝ) :
    HasFDerivAt (fun x => (forestMatrix ℝ N Ω *ᵥ x) ⬝ᵥ
      (W *ᵥ (forestMatrix ℝ N Ω *ᵥ x)))
      ((2 : ℝ) • QuadraticResponse.sourceCovector N (forestGram N Ω W *ᵥ ξ)) ξ := by
  have he : (fun x => (forestMatrix ℝ N Ω *ᵥ x) ⬝ᵥ
      (W *ᵥ (forestMatrix ℝ N Ω *ᵥ x)))=fun x => x ⬝ᵥ (forestGram N Ω W *ᵥ x) := by
    funext x
    exact forest_gram_mixed N Ω W x x
  rw [he]
  exact QuadraticResponse.symmetric_quadratic_hasFDerivAt N (forestGram N Ω W)
    (forest_gram_symmetric N Ω W hW) ξ

theorem continuous_gram_bilinear (N : ℕ) (c e : Fin N → ℝ) :
    (∫ x in (0 : ℝ)..1, weightedProfile N (cutoffCoefficients N c) x*
      weightedProfile N (cutoffCoefficients N e) x)=c ⬝ᵥ (continuousGram N *ᵥ e) := by
  have he (x : ℝ) : weightedProfile N (cutoffCoefficients N c) x*
      weightedProfile N (cutoffCoefficients N e) x=
      ∑ i : Fin N, ∑ j : Fin N, (c i*e j)*
        (weightedProfile N (cutoffCoefficients N (Pi.single i 1)) x*
          weightedProfile N (cutoffCoefficients N (Pi.single j 1)) x) := by
    simp only [weighted_profile_basis]
    simp only [weighted_profile_fin]
    rw [show (2*(∑ i : Fin N, c i*CollisionRampEnergy.midpointRow (i.val+1) x))*
      (2*(∑ j : Fin N, e j*CollisionRampEnergy.midpointRow (j.val+1) x))=
      4*((∑ i : Fin N, c i*CollisionRampEnergy.midpointRow (i.val+1) x)*
        (∑ j : Fin N, e j*CollisionRampEnergy.midpointRow (j.val+1) x)) by ring]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hint (i j : Fin N) : IntervalIntegrable (fun x => (c i*e j)*
      (weightedProfile N (cutoffCoefficients N (Pi.single i 1)) x*
        weightedProfile N (cutoffCoefficients N (Pi.single j 1)) x)) volume 0 1 :=
    (weighted_product_interval_integrable N (cutoffCoefficients N (Pi.single i 1))
      (cutoffCoefficients N (Pi.single j 1)) 0 1).const_mul _
  have hrow (i : Fin N) : IntervalIntegrable (fun x => ∑ j : Fin N, (c i*e j)*
      (weightedProfile N (cutoffCoefficients N (Pi.single i 1)) x*
        weightedProfile N (cutoffCoefficients N (Pi.single j 1)) x)) volume 0 1 := by
    exact ⟨integrable_finsetSum _ (fun j _ => (hint i j).1),
      integrable_finsetSum _ (fun j _ => (hint i j).2)⟩
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hrow i)]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint i j)]
  simp only [intervalIntegral.integral_const_mul, ← continuous_gram_entry]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem continuous_forest_chart (N Ω : ℕ) (ξ η : Fin N → ℝ) :
    (∫ x in (0 : ℝ)..1,
      weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ ξ)) x*
        weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ η)) x)=
      ξ ⬝ᵥ (forestGram N Ω (continuousGram N) *ᵥ η) := by
  rw [continuous_gram_bilinear, forest_gram_mixed]

theorem sampled_forest_chart (N Ω : ℕ) {Q : ℕ} (hQ : 0 < Q) (ξ η : Fin N → ℝ) :
    (Q : ℝ)*sampledWork N Q
      (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ ξ))
      (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ η))=
        ξ ⬝ᵥ (forestGram N Ω (sampledGram N Q) *ᵥ η) := by
  rw [← sampled_gram_mixed_normalized N hQ, forest_gram_mixed]

theorem continuous_gram_symmetric (N : ℕ) (i j : Fin N) :
    continuousGram N i j=continuousGram N j i := by
  simp only [continuousGram, Nat.gcd_comm]
  ring

theorem sampler_gram_symmetric (N Q : ℕ) (i j : Fin N) :
    sampledGram N Q i j=sampledGram N Q j i := by
  rw [sampled_gram_entry, sampled_gram_entry]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem continuous_forest_hasFDerivAt (N Ω : ℕ) (ξ : Fin N → ℝ) :
    HasFDerivAt (fun c => ∫ x in (0 : ℝ)..1,
      weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ c)) x^2)
      ((2 : ℝ) • QuadraticResponse.sourceCovector N (forestGram N Ω (continuousGram N) *ᵥ ξ)) ξ := by
  have he : (fun c => ∫ x in (0 : ℝ)..1,
      weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ c)) x^2)=
      fun c => c ⬝ᵥ (forestGram N Ω (continuousGram N) *ᵥ c) := by
    funext c
    simpa only [pow_two] using continuous_forest_chart N Ω c c
  rw [he]
  exact QuadraticResponse.symmetric_quadratic_hasFDerivAt N _
    (forest_gram_symmetric N Ω _ (continuous_gram_symmetric N)) ξ

theorem sampled_forest_hasFDerivAt (N Ω Q : ℕ) (ξ : Fin N → ℝ) :
    HasFDerivAt (fun c => ∑ a : Fin Q,
      weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ c))
        ((a.val : ℝ)/(Q : ℝ))^2)
      ((2 : ℝ) • QuadraticResponse.sourceCovector N (forestGram N Ω (sampledGram N Q) *ᵥ ξ)) ξ := by
  have he : (fun c => ∑ a : Fin Q,
      weightedProfile N (cutoffCoefficients N (forestMatrix ℝ N Ω *ᵥ c))
        ((a.val : ℝ)/(Q : ℝ))^2)=fun c => c ⬝ᵥ (forestGram N Ω (sampledGram N Q) *ᵥ c) := by
    funext c
    rw [← forest_gram_mixed, sampled_gram_mixed]
    simp only [pow_two]
  rw [he]
  exact QuadraticResponse.symmetric_quadratic_hasFDerivAt N _
    (forest_gram_symmetric N Ω _ (sampler_gram_symmetric N Q)) ξ

end NField.ResetForests.ResetMasks
