/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeProjection
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite native probe synthesis and its actual Gram operator

The probes are vectors in the reciprocal-weight model. Coefficient vectors
use Mathlib's Euclidean space; zero and dependent probes are allowed.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityFiniteGram
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection
variable {ι : Type*} [Fintype ι]

/-- Actual finite probe synthesis. -/
def synthesis (v : ι → NativeHilbert) : EuclideanSpace ℝ ι →ₗ[ℝ] NativeHilbert where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

/-- Actual signed readings against every prescribed probe. -/
def readings (v : ι → NativeHilbert) : NativeHilbert →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun r := WithLp.toLp 2 (fun i => inner ℝ r (v i))
  map_add' x y := by ext i; simp [inner_add_left]
  map_smul' c x := by ext i; simp [real_inner_smul_left]

@[simp] theorem readings_apply (v : ι → NativeHilbert) (r : NativeHilbert) (i : ι) :
    readings v r i = inner ℝ r (v i) := rfl

/-- Signed response of a synthesized vector. -/
theorem inner_synthesis (v : ι → NativeHilbert) (r : NativeHilbert) (x : EuclideanSpace ℝ ι) :
    inner ℝ r (synthesis v x) = inner ℝ (readings v r) x := by
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right,
    PiLp.inner_apply, readings_apply, RCLike.inner_apply, conj_trivial]

/-- The literal Gram operator `K x`, with entries `⟪vᵢ,vⱼ⟫`. -/
def gram (v : ι → NativeHilbert) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (readings v).comp (synthesis v)

/-- Title: `The native Gram operator has the literal probe inner products`. -/
theorem gram_apply (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) (i : ι) :
    gram v x i = ∑ j, inner ℝ (v i) (v j) * x j := by
  simp only [gram, LinearMap.comp_apply, readings_apply, synthesis, LinearMap.coe_mk,
    AddHom.coe_mk, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  ring

theorem gram_inner (v : ι → NativeHilbert) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gram v x) y = inner ℝ (synthesis v x) (synthesis v y) :=
  (inner_synthesis v (synthesis v x) y).symm

theorem gram_symmetric (v : ι → NativeHilbert) : (gram v).IsSymmetric := by
  intro x y
  calc
    inner ℝ (gram v x) y = inner ℝ (synthesis v x) (synthesis v y) := gram_inner v x y
    _ = inner ℝ (synthesis v y) (synthesis v x) := real_inner_comm _ _
    _ = inner ℝ (gram v y) x := (gram_inner v y x).symm
    _ = inner ℝ x (gram v y) := real_inner_comm _ _

/-- Title: `The native Gram quadratic form is synthesis energy`. -/
theorem gram_quadratic (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    inner ℝ (gram v x) x = ‖synthesis v x‖^2 := by
  rw [gram_inner, real_inner_self_eq_norm_sq]

theorem gram_nonneg (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    0 ≤ inner ℝ (gram v x) x := by rw [gram_quadratic]; positivity

/-- The actual finite probe space, even when the probes are dependent. -/
def probeSpace (v : ι → NativeHilbert) : Submodule ℝ NativeHilbert :=
  Submodule.span ℝ (Set.range v)

instance probeSpace_finiteDimensional (v : ι → NativeHilbert) :
    FiniteDimensional ℝ (probeSpace v) := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)

theorem probe_mem (v : ι → NativeHilbert) (i : ι) : v i ∈ probeSpace v :=
  Submodule.subset_span (Set.mem_range_self i)

theorem synthesis_mem (v : ι → NativeHilbert) (x : EuclideanSpace ℝ ι) :
    synthesis v x ∈ probeSpace v := by
  apply Submodule.sum_mem
  intro i _
  exact (probeSpace v).smul_mem (x i) (probe_mem v i)

theorem probeSpace_le (v : ι → NativeHilbert) (S : Submodule ℝ NativeHilbert)
    (hv : ∀i, v i∈S) : probeSpace v≤S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact hv i

/-- Orthogonality to the actual probe space is exactly vanishing signed readings. -/
theorem readings_zero_iff (v : ι → NativeHilbert) (r : NativeHilbert) :
    readings v r=0 ↔ r∈(probeSpace v)ᗮ := by
  constructor
  · intro h
    apply (Submodule.mem_orthogonal' _ _).mpr
    have hle : probeSpace v ≤ (innerSL ℝ r).ker := by
      apply probeSpace_le
      intro i
      have he := congrArg (fun x : EuclideanSpace ℝ ι => x i) h
      simpa using he
    intro w hw
    exact hle hw
  · intro h
    ext i
    exact (Submodule.mem_orthogonal' _ _).mp h _ (probe_mem v i)

/-- Squared norm of the true projection onto all probes. -/
def jointGain (v : ι → NativeHilbert) (r : NativeHilbert) : ℝ :=
  ‖(probeSpace v).starProjection r‖^2

theorem jointGain_nonneg (v : ι → NativeHilbert) (r : NativeHilbert) : 0≤jointGain v r :=
  sq_nonneg _

theorem jointGain_le_native_gain {N M : ℕ} (hNM : N≤M) (v : ι → NativeHilbert)
    (hv : ∀i, v i∈clockSpace M) : jointGain v (UnityNativeHilbert.residual N) ≤ deficit N-deficit M :=
  admitted_projection_gain hNM (probeSpace v) (probeSpace_le v (clockSpace M) hv)

/-- Title: `Every prescribed reading is bounded by joint captured energy`.

 Every scalar or coefficient-vector reading is bounded by the actual joint gain. -/
theorem jointGain_rayleigh (v : ι → NativeHilbert) (r : NativeHilbert)
    (x : EuclideanSpace ℝ ι) :
    (inner ℝ (readings v r) x)^2 ≤ jointGain v r * inner ℝ (gram v x) x := by
  have horth := Submodule.starProjection_inner_eq_zero r (synthesis v x) (synthesis_mem v x)
  rw [inner_sub_left] at horth
  have h := abs_real_inner_le_norm ((probeSpace v).starProjection r) (synthesis v x)
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [← inner_synthesis, gram_quadratic,
    show inner ℝ r (synthesis v x) = inner ℝ ((probeSpace v).starProjection r) (synthesis v x)
      from sub_eq_zero.mp horth]
  simpa only [jointGain, sq_abs, mul_pow] using hsq

end NField.Alignment.UnityFiniteGram
