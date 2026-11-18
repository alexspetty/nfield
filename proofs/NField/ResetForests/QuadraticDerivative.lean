/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SourceMatrices
/-! # The actual full Fréchet derivative of the sampling defect -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.QuadraticResponse

open scoped BigOperators Matrix

def sourceCovector (N : ℕ) (v : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin N, v i • ContinuousLinearMap.proj i

theorem source_covector_apply (N : ℕ) (v w : Fin N → ℝ) :
    sourceCovector N v w=v ⬝ᵥ w := by
  simp [sourceCovector, dotProduct]

def quadraticDifferential (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, A i j •
    (c i • ContinuousLinearMap.proj j+c j • ContinuousLinearMap.proj i)

theorem matrix_quadratic_hasFDerivAt (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℝ) :
    HasFDerivAt (fun x => x ⬝ᵥ (A *ᵥ x)) (quadraticDifferential N A c) c := by
  have he : (fun x : Fin N → ℝ => x ⬝ᵥ (A *ᵥ x))=
      fun x => ∑ i : Fin N, ∑ j : Fin N, A i j*(x i*x j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  unfold quadraticDifferential
  refine HasFDerivAt.fun_sum fun i hi => ?_
  refine HasFDerivAt.fun_sum fun j hj => ?_
  exact ((hasFDerivAt_apply i c).mul (hasFDerivAt_apply j c)).const_mul (A i j)

theorem quadratic_differential_apply (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (c w : Fin N → ℝ) :
    quadraticDifferential N A c w=w ⬝ᵥ (A *ᵥ c)+c ⬝ᵥ (A *ᵥ w) := by
  simp only [quadraticDifferential, sum_apply,
    smul_apply, add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem symmetric_quadratic_differential (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i j, A i j=A j i) (c : Fin N → ℝ) :
    quadraticDifferential N A c=(2 : ℝ) • sourceCovector N (A *ᵥ c) := by
  have hAT : Aᵀ=A := by
    ext i j
    exact hA j i
  ext w
  rw [quadratic_differential_apply]
  simp only [smul_apply, source_covector_apply, smul_eq_mul]
  have hs := Matrix.dotProduct_transpose_mulVec A c w
  rw [hAT] at hs
  rw [hs, dotProduct_comm w (A *ᵥ c)]
  ring

theorem symmetric_quadratic_hasFDerivAt (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i j, A i j=A j i) (c : Fin N → ℝ) :
    HasFDerivAt (fun x => x ⬝ᵥ (A *ᵥ x)) ((2 : ℝ) • sourceCovector N (A *ᵥ c)) c := by
  rw [← symmetric_quadratic_differential N A hA c]
  exact matrix_quadratic_hasFDerivAt N A c

theorem sampling_hasFDerivAt (N Q : ℕ) (c : Fin N → ℝ) :
    HasFDerivAt (sourceDefect N Q)
      ((2 : ℝ) • sourceCovector N (samplingDefectMatrix N Q *ᵥ c)) c := by
  have he : sourceDefect N Q=fun x => x ⬝ᵥ (samplingDefectMatrix N Q *ᵥ x) :=
    funext (sampling_matrix_quadratic N Q)
  rw [he]
  exact symmetric_quadratic_hasFDerivAt N (samplingDefectMatrix N Q)
    (sampling_matrix_symmetric N Q) c

theorem sampling_exact_increment (N Q : ℕ) (c w : Fin N → ℝ) :
    sourceDefect N Q (c+w)=sourceDefect N Q c+
      2*((samplingDefectMatrix N Q *ᵥ c) ⬝ᵥ w)+sourceDefect N Q w := by
  have hAT : (samplingDefectMatrix N Q)ᵀ=samplingDefectMatrix N Q := by
    ext i j
    exact sampling_matrix_symmetric N Q j i
  have hs := Matrix.dotProduct_transpose_mulVec (samplingDefectMatrix N Q) c w
  rw [hAT] at hs
  simp only [sampling_matrix_quadratic, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [hs, dotProduct_comm w (samplingDefectMatrix N Q *ᵥ c)]
  ring

theorem full_sampling_half_gradient {p : ℕ} (hp : p.Prime) :
    HasFDerivAt (sourceDefect (p-1) (p^2))
      ((2 : ℝ) • sourceCovector (p-1)
        (fun i => (((p-1 : ℕ) : ℝ)+
          (clockMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i-
          (curvatureMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i)/((p^2 : ℕ) : ℝ)))
      (fun _ => (1 : ℝ)) := by
  have h := sampling_hasFDerivAt (p-1) (p^2) (fun _ => (1 : ℝ))
  rw [sampling_half_gradient_vector hp] at h
  exact h

theorem full_sampling_fderiv {p : ℕ} (hp : p.Prime) :
    fderiv ℝ (sourceDefect (p-1) (p^2)) (fun _ => (1 : ℝ))=
      (2 : ℝ) • sourceCovector (p-1)
        (fun i => (((p-1 : ℕ) : ℝ)+
          (clockMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i-
          (curvatureMatrix (p-1) (p^2) *ᵥ (fun _ => (1 : ℝ))) i)/((p^2 : ℕ) : ℝ)) :=
  (full_sampling_half_gradient hp).fderiv

end NField.ResetForests.QuadraticResponse
