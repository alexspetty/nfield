/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PositiveQuotientSpectrum
import NField.Alignment.TheStructureThatSurvives

/-! Literal particle degrees and the normalized finite quotient. -/

namespace NField.Alignment.ConcreteCollisionBlocks

open scoped BigOperators
open Matrix TheStructureThatSurvives ExponentialDistanceKernel ExponentialSpectralQuotient

noncomputable def population {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (α : κ) : ℝ := labelPopulation label α

noncomputable def blockScale {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (α : κ) : ℝ := Real.sqrt (population label α)

noncomputable def particleDegree {ι κ : Type*} [Fintype ι]
    (label : ι → κ) (x : κ → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  ∑ j, kernel (x ∘ label) τ i j

noncomputable def particleNormalized {ι κ : Type*} [Fintype ι]
    (label : ι → κ) (x : κ → ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  fun i j => kernel (x ∘ label) τ i j /
    Real.sqrt (particleDegree label x τ i * particleDegree label x τ j)

noncomputable def blockEmbedding {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) : Matrix ι κ ℝ :=
  fun i α => if label i = α then (blockScale label α)⁻¹ else 0

theorem population_pos {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (hsurj : Function.Surjective label) (α : κ) : 0 < population label α := by
  obtain ⟨i, hi⟩ := hsurj α
  haveI : Nonempty (LabelFiber label α) := ⟨⟨i, hi⟩⟩
  change 0 < (Fintype.card (LabelFiber label α) : ℝ)
  exact_mod_cast Fintype.card_pos (α := LabelFiber label α)

theorem blockScale_pos {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (hsurj : Function.Surjective label) (α : κ) : 0 < blockScale label α :=
  Real.sqrt_pos.mpr (population_pos label hsurj α)

theorem blockScale_sq {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (α : κ) : blockScale label α ^ 2 = labelPopulation label α :=
  Real.sq_sqrt (Nat.cast_nonneg _)

/-- Title: `Particle degrees equal their block degrees`. -/
theorem particleDegree_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (x : κ → ℝ) (τ : ℝ) (i : ι) :
    particleDegree label x τ i = degree x (population label) τ (label i) := by
  classical
  rw [particleDegree, ← Fintype.sum_fiberwise label]
  unfold degree
  apply Finset.sum_congr rfl
  intro α hα
  have hp (j : LabelFiber label α) :
      kernel (x ∘ label) τ i j = kernel x τ (label i) α := by
    simp only [kernel, Function.comp_apply, j.property]
  simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- Title: `The literal particle affinity is the normalized block kernel`.

The literal normalized particle affinity is the previously proved block kernel. -/
theorem particleNormalized_eq_blockKernel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (hsurj : Function.Surjective label) (x : κ → ℝ) (τ : ℝ) :
    particleNormalized label x τ = normalizedBlockKernel label (blockScale label)
      (quotient x (population label) τ) := by
  ext i j
  simp only [particleNormalized, normalizedBlockKernel, quotient, particleDegree_eq,
    blockScale, Real.sqrt_mul (population_pos label hsurj _).le]
  change kernel x τ (label i) (label j) / _ = _
  have hi : Real.sqrt (population label (label i)) ≠ 0 := ne_of_gt (blockScale_pos label hsurj _)
  have hj : Real.sqrt (population label (label j)) ≠ 0 := ne_of_gt (blockScale_pos label hsurj _)
  field_simp

theorem blockEmbedding_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (v : κ → ℝ) :
    blockEmbedding label *ᵥ v = normalizedBlockLift label (blockScale label) v := by
  ext i
  simp [mulVec, dotProduct, blockEmbedding, normalizedBlockLift, div_eq_mul_inv, mul_comm]

theorem blockEmbedding_transpose_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (v : ι → ℝ) :
    (blockEmbedding label)ᵀ *ᵥ v = normalizedBlockCoordinate label (blockScale label) v := by
  classical
  ext α
  simp only [mulVec, dotProduct, transpose_apply, blockEmbedding, normalizedBlockCoordinate,
    labelBlockSum, div_eq_mul_inv]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => label i = α))
    (by simp) (fun i => v i), Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp [mul_comm]

/-- Title: `Normalized block indicators are orthonormal`. -/
theorem blockEmbedding_orthonormal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (hsurj : Function.Surjective label) :
    (blockEmbedding label)ᵀ * blockEmbedding label = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← mulVec_mulVec, blockEmbedding_mulVec, blockEmbedding_transpose_mulVec, one_mulVec]
  ext α
  exact normalizedBlockCoordinate_lift label (blockScale label)
    (fun α => ne_of_gt (blockScale_pos label hsurj α)) (blockScale_sq label) v α

/-- Title: `The concrete block embedding gives the quotient compression`.

The columns of the concrete block embedding give the exact quotient compression. -/
theorem particleNormalized_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (label : ι → κ) (hsurj : Function.Surjective label) (x : κ → ℝ) (τ : ℝ) :
    particleNormalized label x τ = blockEmbedding label * quotient x (population label) τ *
      (blockEmbedding label)ᵀ := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [particleNormalized_eq_blockKernel label hsurj x τ, ← mulVec_mulVec,
    ← mulVec_mulVec, blockEmbedding_transpose_mulVec, blockEmbedding_mulVec]
  ext i
  exact normalizedBlockKernel_mulVec label (blockScale label) _
    (fun α => ne_of_gt (blockScale_pos label hsurj α)) v i

end NField.Alignment.ConcreteCollisionBlocks
