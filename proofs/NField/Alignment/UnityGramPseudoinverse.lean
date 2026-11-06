/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityFiniteGram

/-!
# The actual Moore--Penrose certificate for finite native probes

Mathlib diagonalizes the real symmetric Gram operator. Inverting each
nonzero eigenvalue and leaving zero eigenvalues at zero gives the actual
Moore--Penrose inverse, including dependent and zero probes.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityGramPseudoinverse
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityFiniteGram
variable {ι : Type*} [Fintype ι]

abbrev EigenIndex (ι : Type*) [Fintype ι] := Fin (Module.finrank ℝ (EuclideanSpace ℝ ι))

def eigenBasis (v : ι → NativeHilbert) :
    OrthonormalBasis (EigenIndex ι) ℝ (EuclideanSpace ℝ ι) :=
  (gram_symmetric v).eigenvectorBasis rfl

def eigenvalue (v : ι → NativeHilbert) : EigenIndex ι → ℝ :=
  (gram_symmetric v).eigenvalues rfl

theorem gram_eigenvector (v : ι → NativeHilbert) (i : EigenIndex ι) :
    gram v (eigenBasis v i) = eigenvalue v i • eigenBasis v i :=
  (gram_symmetric v).apply_eigenvectorBasis rfl i

theorem gram_coordinate (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) (i : EigenIndex ι) :
    (eigenBasis v).repr (gram v x) i = eigenvalue v i * (eigenBasis v).repr x i :=
  (gram_symmetric v).eigenvectorBasis_apply_self_apply rfl x i

theorem eigenvalue_nonneg (v : ι → NativeHilbert) (i : EigenIndex ι) : 0≤eigenvalue v i := by
  have h := gram_nonneg v (eigenBasis v i)
  rw [gram_eigenvector, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigenBasis v).norm_eq_one, one_pow, mul_one] at h
  exact h

/-- Spectral Moore--Penrose inverse of the literal finite native Gram. -/
def pseudoInverse (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (eigenBasis v).repr.symm (WithLp.toLp 2
    (fun i => (eigenvalue v i)⁻¹ * (eigenBasis v).repr x i))

@[simp] theorem pseudo_coordinate (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) (i : EigenIndex ι) :
    (eigenBasis v).repr (pseudoInverse v x) i = (eigenvalue v i)⁻¹ * (eigenBasis v).repr x i := by
  simp [pseudoInverse]

theorem pseudo_add (v : ι → NativeHilbert) (x y : EuclideanSpace ℝ ι) :
    pseudoInverse v (x+y)=pseudoInverse v x+pseudoInverse v y := by
  apply (eigenBasis v).repr.injective
  ext i
  simp [pseudo_coordinate, mul_add]

theorem pseudo_smul (v : ι → NativeHilbert) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    pseudoInverse v (c • x)=c • pseudoInverse v x := by
  apply (eigenBasis v).repr.injective
  ext i
  simp [pseudo_coordinate, mul_left_comm]

def pseudoLinear (v : ι → NativeHilbert) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := pseudoInverse v
  map_add' := pseudo_add v
  map_smul' := pseudo_smul v

/-- Title: `First Penrose identity for the actual native Gram`.

 First Penrose identity. -/
theorem gram_pseudo_gram (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    gram v (pseudoInverse v (gram v x))=gram v x := by
  apply (eigenBasis v).repr.injective
  ext i
  simp only [gram_coordinate, pseudo_coordinate]
  by_cases h : eigenvalue v i=0
  · simp [h]
  · field_simp

/-- Title: `Second Penrose identity for the actual native Gram`.

 Second Penrose identity. -/
theorem pseudo_gram_pseudo (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    pseudoInverse v (gram v (pseudoInverse v x))=pseudoInverse v x := by
  apply (eigenBasis v).repr.injective
  ext i
  simp only [gram_coordinate, pseudo_coordinate]
  by_cases h : eigenvalue v i=0
  · simp [h]
  · field_simp

theorem gram_pseudo_commute (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    gram v (pseudoInverse v x)=pseudoInverse v (gram v x) := by
  apply (eigenBasis v).repr.injective
  ext i
  simp only [gram_coordinate, pseudo_coordinate]
  ring

/-- The spectral inverse is real symmetric. -/
theorem pseudo_symmetric (v : ι → NativeHilbert) : (pseudoLinear v).IsSymmetric := by
  intro x y
  rw [← (eigenBasis v).repr.inner_map_map, ← (eigenBasis v).repr.inner_map_map x]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change (eigenBasis v).repr y i * (eigenBasis v).repr (pseudoInverse v x) i =
    (eigenBasis v).repr (pseudoInverse v y) i * (eigenBasis v).repr x i
  rw [pseudo_coordinate, pseudo_coordinate]
  ring

/-- Title: `Both Gram inverse products are self-adjoint`.

 Third and fourth Penrose identities, in their equivalent self-adjoint form. -/
theorem gram_pseudo_symmetric (v : ι → NativeHilbert) :
    ((gram v).comp (pseudoLinear v)).IsSymmetric ∧
    ((pseudoLinear v).comp (gram v)).IsSymmetric := by
  have hs : ((gram v).comp (pseudoLinear v)).IsSymmetric := by
    intro x y
    change inner ℝ (gram v (pseudoInverse v x)) y = inner ℝ x (gram v (pseudoInverse v y))
    rw [gram_symmetric v]
    change inner ℝ (pseudoLinear v x) (gram v y) = _
    rw [pseudo_symmetric v]
    change inner ℝ x (pseudoInverse v (gram v y)) = _
    rw [gram_pseudo_commute]
  refine ⟨hs, ?_⟩
  intro x y
  change inner ℝ (pseudoInverse v (gram v x)) y = inner ℝ x (pseudoInverse v (gram v y))
  rw [← gram_pseudo_commute, ← gram_pseudo_commute]
  exact hs x y

/-- A null Gram eigenvector synthesizes to the zero native vector. -/
theorem null_eigen_synthesis (v : ι → NativeHilbert) (i : EigenIndex ι)
    (hi : eigenvalue v i=0) : synthesis v (eigenBasis v i)=0 := by
  have h := gram_quadratic v (eigenBasis v i)
  rw [gram_eigenvector, hi, zero_smul, inner_zero_left] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)

/-- Actual signed readings have no component in the null Gram eigenspaces. -/
theorem null_eigen_reading (v : ι → NativeHilbert) (r : NativeHilbert)
    (i : EigenIndex ι) (hi : eigenvalue v i=0) :
    (eigenBasis v).repr (readings v r) i=0 := by
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, ← inner_synthesis,
    null_eigen_synthesis v i hi, inner_zero_right]

/-- The pseudoinverse solves the normal equations for the actual readings. -/
theorem gram_pseudo_readings (v : ι → NativeHilbert) (r : NativeHilbert) :
    gram v (pseudoInverse v (readings v r)) = readings v r := by
  apply (eigenBasis v).repr.injective
  ext i
  rw [gram_coordinate, pseudo_coordinate]
  by_cases hi : eigenvalue v i=0
  · rw [null_eigen_reading v r i hi]
    ring
  · field_simp

/-- The solved native normal equations give the true probe-space projection. -/
theorem projection_eq_pseudo_synthesis (v : ι → NativeHilbert) (r : NativeHilbert) :
    (probeSpace v).starProjection r = synthesis v (pseudoInverse v (readings v r)) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (synthesis_mem v _)
  apply (readings_zero_iff v _).mp
  rw [map_sub]
  change readings v r-gram v (pseudoInverse v (readings v r))=0
  rw [gram_pseudo_readings, sub_self]

/-- Title: `The pseudoinverse certificate equals actual projected energy`.

 The literal Moore--Penrose quadratic certificate is the actual projected energy. -/
theorem jointGain_eq_pseudoinverse (v : ι → NativeHilbert) (r : NativeHilbert) :
    jointGain v r = inner ℝ (readings v r) (pseudoInverse v (readings v r)) := by
  rw [jointGain, projection_eq_pseudo_synthesis, ← gram_quadratic, gram_pseudo_readings]

/-- Title: `The full native gain certificate allows dependent probes`.

 Full native gain certificate, including dependent and zero probes. -/
theorem pseudoinverse_native_gain {N M : ℕ} (hNM : N≤M) (v : ι → NativeHilbert)
    (hv : ∀i, v i∈clockSpace M) :
    0 ≤ inner ℝ (readings v (UnityNativeHilbert.residual N))
      (pseudoInverse v (readings v (UnityNativeHilbert.residual N))) ∧
    inner ℝ (readings v (UnityNativeHilbert.residual N))
      (pseudoInverse v (readings v (UnityNativeHilbert.residual N))) ≤ deficit N-deficit M := by
  rw [← jointGain_eq_pseudoinverse]
  exact ⟨jointGain_nonneg _ _, jointGain_le_native_gain hNM v hv⟩

end NField.Alignment.UnityGramPseudoinverse
