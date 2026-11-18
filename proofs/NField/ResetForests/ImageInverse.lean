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
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
/-! # Inverse on the image and zero on its orthogonal complement

Finite-dimensional real spectral calculus inverts every nonzero eigenvalue
and retains the zero eigenspace as zero. The image and kernel statements
below identify this construction with the inverse used by the record lifts.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def imageInverse (H : Matrix ι ι ℝ) (hH : H.IsHermitian) : Matrix ι ι ℝ :=
  hH.cfc (fun x => x⁻¹)

theorem spectral_function_mul (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (f g : ℝ → ℝ) :
    hH.cfc f * hH.cfc g = hH.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1

theorem spectral_function_identity (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    hH.cfc (fun x => x) = H := by
  exact hH.spectral_theorem.symm

theorem spectral_function_hermitian (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (hH.cfc f).IsHermitian := by
  unfold Matrix.IsHermitian.cfc
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hH.eigenvalues) : Matrix ι ι ℝ).IsHermitian :=
    Matrix.isHermitian_diagonal _
  exact hd.isSelfAdjoint.map (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hH.eigenvectorUnitary)

theorem image_inverse_hermitian (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    (imageInverse H hH).IsHermitian := spectral_function_hermitian H hH _

theorem image_inverse_commute (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    H * imageInverse H hH = imageInverse H hH * H := by
  have h : hH.cfc (fun x => x) * hH.cfc (fun x => x⁻¹) =
      hH.cfc (fun x => x⁻¹) * hH.cfc (fun x => x) := by
    rw [spectral_function_mul, spectral_function_mul]
    congr 1
    ext x
    exact mul_comm _ _
  simpa only [imageInverse, spectral_function_identity] using h

theorem image_inverse_inner (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    H * imageInverse H hH * H = H := by
  have h : hH.cfc (fun x => x) * hH.cfc (fun x => x⁻¹) * hH.cfc (fun x => x) =
      hH.cfc (fun x => x) := by
    rw [spectral_function_mul, spectral_function_mul]
    congr 1
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  simpa only [imageInverse, spectral_function_identity] using h

theorem image_inverse_outer (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    imageInverse H hH * H * imageInverse H hH = imageInverse H hH := by
  have h : hH.cfc (fun x => x⁻¹) * hH.cfc (fun x => x) * hH.cfc (fun x => x⁻¹) =
      hH.cfc (fun x => x⁻¹) := by
    rw [spectral_function_mul, spectral_function_mul]
    congr 1
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  simpa only [imageInverse, spectral_function_identity] using h

theorem image_inverse_mul_mem_range (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (y : ι → ℝ) :
    imageInverse H hH *ᵥ y ∈ LinearMap.range H.mulVecLin := by
  refine ⟨imageInverse H hH *ᵥ (imageInverse H hH *ᵥ y), ?_⟩
  change H *ᵥ (imageInverse H hH *ᵥ (imageInverse H hH *ᵥ y)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, image_inverse_commute, image_inverse_outer]

theorem image_inverse_on_image (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (y : ι → ℝ)
    (hy : y ∈ LinearMap.range H.mulVecLin) : H *ᵥ (imageInverse H hH *ᵥ y) = y := by
  obtain ⟨x, rfl⟩ := hy
  change H *ᵥ (imageInverse H hH *ᵥ (H *ᵥ x)) = H *ᵥ x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, image_inverse_inner]

theorem image_inverse_zero_on_kernel (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (x : ι → ℝ)
    (hx : H *ᵥ x = 0) : imageInverse H hH *ᵥ x = 0 := by
  calc
    imageInverse H hH *ᵥ x = (imageInverse H hH * H * imageInverse H hH) *ᵥ x := by
      rw [image_inverse_outer]
    _ = imageInverse H hH *ᵥ (imageInverse H hH *ᵥ (H *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        image_inverse_commute, ← Matrix.mul_assoc]
    _ = 0 := by rw [hx, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem image_inverse_zero_on_orthogonal (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (x : ι → ℝ)
    (hx : ∀ y ∈ LinearMap.range H.mulVecLin, y ⬝ᵥ x = 0) : imageInverse H hH *ᵥ x = 0 := by
  apply image_inverse_zero_on_kernel H hH x
  ext i
  have h := hx (H *ᵥ Pi.single i 1) ⟨Pi.single i 1, rfl⟩
  have hs : Hᵀ = H := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hH
  rw [dotProduct_comm, ← hs, Matrix.dotProduct_transpose_mulVec, single_dotProduct, one_mul] at h
  exact h

end NField.ResetForests.RecordGeometry
