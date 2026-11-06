/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityDetectorBandCost
import NField.Alignment.UnityStableCorrection
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Literal native Gram trace and signed-reading certificates -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityGramCosts
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityFiniteGram UnityGramPseudoinverse
open UnityStableCorrection UnityPrescribedDetectors UnityDetectorBandCost
variable {ι : Type*} [Fintype ι]

/-- The finite matrix of the actual native probe inner products. -/
def gramMatrix (v : ι → NativeHilbert) : Matrix ι ι ℝ := fun i j => inner ℝ (v i) (v j)

omit [Fintype ι] in
theorem gramMatrix_diagonal (v : ι → NativeHilbert) (i : ι) :
    gramMatrix v i i=‖v i‖^2 := real_inner_self_eq_norm_sq _

/-- Title: `The literal native Gram trace is the sum of probe energies`. -/
theorem gramMatrix_trace (v : ι → NativeHilbert) :
    Matrix.trace (gramMatrix v)=∑ i, ‖v i‖^2 := by
  simp only [Matrix.trace, Matrix.diag, gramMatrix_diagonal]

theorem gramMatrix_trace_nonneg (v : ι → NativeHilbert) :
    0≤Matrix.trace (gramMatrix v) := by
  rw [gramMatrix_trace]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Finite Cauchy--Schwarz gives the literal trace ceiling, including dependent probes. -/
theorem synthesis_cost (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    ‖synthesis v x‖^2≤Matrix.trace (gramMatrix v)*‖x‖^2 := by
  have hn : ‖synthesis v x‖≤∑ i, |x i| * ‖v i‖ := by
    simpa only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, norm_smul,
      Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i => x i • v i)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |x i|) (fun i => ‖v i‖)
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)))).mpr hn
  rw [gramMatrix_trace, EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs, mul_comm] using hn2.trans hs

theorem gram_cost (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    inner ℝ (gram v x) x≤Matrix.trace (gramMatrix v)*‖x‖^2 := by
  rw [gram_quadratic]
  exact synthesis_cost v x

theorem eigenvalue_le_trace (v : ι → NativeHilbert) (i : EigenIndex ι) :
    eigenvalue v i≤Matrix.trace (gramMatrix v) := by
  have h := gram_cost v (eigenBasis v i)
  rw [gram_eigenvector, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigenBasis v).norm_eq_one, one_pow, mul_one, mul_one] at h
  exact h

/-- The actual largest Gram eigenvalue, with the empty matrix assigned zero. -/
def largestEigenvalue (v : ι → NativeHilbert) : ℝ :=
  if h : (Finset.univ : Finset (EigenIndex ι)).Nonempty then
    Finset.univ.sup' h (eigenvalue v) else 0

/-- Title: `The largest actual Gram eigenvalue is bounded by its trace`. -/
theorem largestEigenvalue_le_trace (v : ι → NativeHilbert) :
    largestEigenvalue v≤Matrix.trace (gramMatrix v) := by
  classical
  unfold largestEigenvalue
  split_ifs
  · exact Finset.sup'_le _ _ (fun i _ => eigenvalue_le_trace v i)
  · exact gramMatrix_trace_nonneg v

/-- Title: `Signed reading energy is bounded by the literal Gram trace`.

 Squared signed readings obey the same literal trace ceiling. -/
theorem readings_cost (v : ι → NativeHilbert) (r : NativeHilbert) :
    ‖readings v r‖^2≤Matrix.trace (gramMatrix v)*‖r‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, gramMatrix_trace, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg r)
    (norm_nonneg (v i)))).mpr (abs_real_inner_le_norm r (v i))
  simpa only [readings_apply, sq_abs, mul_pow, mul_comm] using h

/-- A positive Gram ceiling gives a joint-gain certificate from all signed readings. -/
theorem jointGain_readings_lower (v : ι → NativeHilbert) (r : NativeHilbert)
    (C : ℝ) (hC : 0<C)
    (hc : ∀x, inner ℝ (gram v x) x≤C*‖x‖^2) :
    ‖readings v r‖^2/C≤jointGain v r := by
  have h := stable_joint_gain v r (readings v r) C 0 hC hc (by simp)
  simpa only [sub_zero, max_eq_left (norm_nonneg _)] using h

theorem jointGain_rayleigh_quotient (v : ι → NativeHilbert) (r : NativeHilbert)
    (x : EuclideanSpace ℝ ι) (hx : 0 < inner ℝ (gram v x) x) :
    |inner ℝ (readings v r) x|^2/inner ℝ (gram v x) x≤jointGain v r := by
  apply (div_le_iff₀ hx).mpr
  simpa only [sq_abs] using jointGain_rayleigh v r x

/-- Zero-cost scalar quotients are zero by the real field's total division convention. -/
theorem jointGain_scalar_quotient (v : ι → NativeHilbert) (r : NativeHilbert) (i : ι) :
    (inner ℝ r (v i))^2/‖v i‖^2≤jointGain v r := by
  classical
  by_cases h : v i=0
  · simp only [h, inner_zero_right, zero_pow (by omega : 2≠0), norm_zero, div_zero]
    exact jointGain_nonneg v r
  have hp : 0<‖v i‖^2 := sq_pos_of_pos (norm_pos_iff.mpr h)
  have ho := Submodule.starProjection_inner_eq_zero r (v i) (probe_mem v i)
  rw [inner_sub_left] at ho
  have hb := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))).mpr (abs_real_inner_le_norm ((probeSpace v).starProjection r) (v i))
  apply (div_le_iff₀ hp).mpr
  rw [show inner ℝ r (v i)=inner ℝ ((probeSpace v).starProjection r) (v i) from sub_eq_zero.mp ho]
  simpa only [jointGain, sq_abs, mul_pow] using hb

theorem detector_trace_le_cost (N : ℕ) :
    Matrix.trace (gramMatrix (detectorFamily N))≤totalCost N := by
  rw [gramMatrix_trace]
  change (∑ h : eligible N, ‖detector N h‖^2)≤∑ h∈eligible N, bandCost N h
  rw [Finset.sum_coe_sort (eligible N) (fun h => ‖detector N h‖^2)]
  exact Finset.sum_le_sum (fun h _ => detector_cost N h)

/-- Title: `The full uniform cost chain for the prescribed detector family`.

 All displayed uniform cost bounds for the paper's exact prescribed detector family. -/
theorem prescribed_uniform_cost (N : ℕ) :
    (∀h : eligible N, gramMatrix (detectorFamily N) h h≤bandCost N h ∧ bandCost N h≤1) ∧
    largestEigenvalue (detectorFamily N)≤Matrix.trace (gramMatrix (detectorFamily N)) ∧
    Matrix.trace (gramMatrix (detectorFamily N))≤totalCost N ∧ totalCost N≤2 := by
  refine ⟨?_, largestEigenvalue_le_trace _, detector_trace_le_cost N, totalCost_le_two N⟩
  intro h
  rw [gramMatrix_diagonal]
  exact ⟨detector_cost N h, UnityProjectionBands.newRoot_cost _⟩

theorem prescribed_gram_ceiling (N : ℕ) (x : EuclideanSpace ℝ (eligible N)) :
    inner ℝ (detectorGram N x) x≤totalCost N*‖x‖^2 :=
  (gram_cost (detectorFamily N) x).trans
    (mul_le_mul_of_nonneg_right (detector_trace_le_cost N) (sq_nonneg _))

theorem prescribed_joint_lower (N : ℕ) (hT : 0<totalCost N) :
    ‖signedReadings N‖^2/totalCost N≤capture N := by
  rw [capture_eq_jointGain]
  exact jointGain_readings_lower (detectorFamily N) _ _ hT (prescribed_gram_ceiling N)

/-- Title: `Joint capture dominates half the squared signed-reading norm`.

 The actual joint gain dominates half the squared signed-reading norm. -/
theorem prescribed_half_lower (N : ℕ) : (1/2:ℝ)*‖signedReadings N‖^2≤capture N := by
  rw [capture_eq_jointGain]
  have hcost : ∀x : EuclideanSpace ℝ (eligible N),
      inner ℝ (gram (detectorFamily N) x) x≤2*‖x‖^2 := fun x =>
    (prescribed_gram_ceiling N x).trans
      (mul_le_mul_of_nonneg_right (totalCost_le_two N) (sq_nonneg _))
  simpa only [div_eq_mul_inv, one_mul, mul_comm, signedReadings] using
    jointGain_readings_lower (detectorFamily N) (UnityNativeHilbert.residual N) 2 (by norm_num) hcost

end NField.Alignment.UnityGramCosts
