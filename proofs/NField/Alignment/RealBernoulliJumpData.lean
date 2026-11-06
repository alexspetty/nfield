/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBernoulliBoundaryLimits
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The actual squared boundary and derivative jumps, including the origin -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealBernoulliJumpData
open scoped BigOperators Topology
open Filter Set CollisionDedekindPairing RealSawtoothLimits RealBernoulliBoundaryLimits CarrierJumpData

def realSlope (N : ℕ) : ℝ := (N : ℝ)*(N+1)

theorem twice_sum_indices (N : ℕ) :
    2*(∑ r ∈ Finset.range N, ((r+1 : ℕ) : ℝ))=realSlope N := by
  induction N with
  | zero => simp [realSlope]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    unfold realSlope at ih ⊢
    push_cast at ih ⊢
    nlinarith

theorem boundary_deriv {N : ℕ} {x : ℝ}
    (hx : ∀ r ∈ Finset.range N, Int.fract (((r+1 : ℕ) : ℝ)*x) ≠ 0) :
    HasDerivAt (realBoundary N) (realSlope N) x := by
  have hs := HasDerivAt.fun_sum (fun r (hr : r ∈ Finset.range N) =>
    (sawtooth_deriv (hx r hr)).comp x ((hasDerivAt_id x).const_mul ((r+1 : ℕ) : ℝ)))
  have h := hs.const_mul 2
  simp only [mul_one,one_mul,Function.comp_apply,twice_sum_indices] at h
  exact h

theorem boundary_deriv_left_eventually (N : ℕ) (x : ℝ) :
    ∀ᶠ y in 𝓝[<] x, HasDerivAt (realBoundary N) (realSlope N) y := by
  have h : ∀ r ∈ Finset.range N, ∀ᶠ y in 𝓝[<] x,
      Int.fract (((r+1 : ℕ) : ℝ)*y) ≠ 0 := by
    intro r hr
    exact (positive_mul_left_limit (by positivity : (0 : ℝ)<((r+1 : ℕ) : ℝ)) x)
      (eventually_fract_ne_left _)
  have hall : ∀ᶠ y in 𝓝[<] x, ∀ r ∈ Finset.range N,
      Int.fract (((r+1 : ℕ) : ℝ)*y) ≠ 0 := by simpa only [Filter.eventually_all_finset] using h
  exact hall.mono fun y hy => boundary_deriv hy

theorem boundary_deriv_right_eventually (N : ℕ) (x : ℝ) :
    ∀ᶠ y in 𝓝[>] x, HasDerivAt (realBoundary N) (realSlope N) y := by
  have h : ∀ r ∈ Finset.range N, ∀ᶠ y in 𝓝[>] x,
      Int.fract (((r+1 : ℕ) : ℝ)*y) ≠ 0 := by
    intro r hr
    exact (positive_mul_right_limit (by positivity : (0 : ℝ)<((r+1 : ℕ) : ℝ)) x)
      (eventually_fract_ne_right _)
  have hall : ∀ᶠ y in 𝓝[>] x, ∀ r ∈ Finset.range N,
      Int.fract (((r+1 : ℕ) : ℝ)*y) ≠ 0 := by simpa only [Filter.eventually_all_finset] using h
  exact hall.mono fun y hy => boundary_deriv hy

theorem square_derivative_left (N : ℕ) (x : ℝ) :
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[<] x)
      (𝓝 (2*realSlope N*(realBoundary N x+(halfJump N x : ℝ)))) := by
  have h := (boundary_left N x).const_mul (2*realSlope N)
  apply h.congr'
  filter_upwards [boundary_deriv_left_eventually N x] with y hy
  rw [(hy.fun_pow 2).deriv]
  ring

theorem square_derivative_right (N : ℕ) (x : ℝ) :
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[>] x)
      (𝓝 (2*realSlope N*(realBoundary N x-(halfJump N x : ℝ)))) := by
  have h := (boundary_right N x).const_mul (2*realSlope N)
  apply h.congr'
  filter_upwards [boundary_deriv_right_eventually N x] with y hy
  rw [(hy.fun_pow 2).deriv]
  ring

/-- Title: `Actual squared-boundary and derivative limits at a rational jump`. -/
theorem rational_square_jump_limits {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    let T : ℝ := cyclicPrefixResponse a k (N%k)
    let M : ℝ := (N/k : ℕ)
    Tendsto (fun y => realBoundary N y^2) (𝓝[<] ((a : ℝ)/k)) (𝓝 ((T+M)^2)) ∧
    Tendsto (fun y => realBoundary N y^2) (𝓝[>] ((a : ℝ)/k)) (𝓝 ((T-M)^2)) ∧
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[<] ((a : ℝ)/k)) (𝓝 (2*realSlope N*(T+M))) ∧
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[>] ((a : ℝ)/k)) (𝓝 (2*realSlope N*(T-M))) ∧
    (T-M)^2-(T+M)^2=-4*M*T ∧
    2*realSlope N*(T-M)-2*realSlope N*(T+M)=-4*realSlope N*M := by
  dsimp only
  refine ⟨(rational_boundary_limits hk hcop).1.pow 2,(rational_boundary_limits hk hcop).2.pow 2,?_,?_,by ring,by ring⟩
  · simpa only [boundary_rational hk hcop,halfJump_rational hk hcop] using square_derivative_left N ((a : ℝ)/k)
  · simpa only [boundary_rational hk hcop,halfJump_rational hk hcop] using square_derivative_right N ((a : ℝ)/k)

/-- Title: `The squared-boundary and derivative jumps at the origin`. -/
theorem origin_square_jump_limits (N : ℕ) :
    realBoundary N 0^2=0 ∧
    Tendsto (fun y => realBoundary N y^2) (𝓝[<] 0) (𝓝 ((N : ℝ)^2)) ∧
    Tendsto (fun y => realBoundary N y^2) (𝓝[>] 0) (𝓝 ((N : ℝ)^2)) ∧
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[<] 0) (𝓝 (2*realSlope N*N)) ∧
    Tendsto (deriv (fun y => realBoundary N y^2)) (𝓝[>] 0) (𝓝 (-2*realSlope N*N)) ∧
    (-2*realSlope N*N)-(2*realSlope N*N)=-4*realSlope N*N := by
  obtain ⟨hb,hl,hr⟩ := origin_boundary_limits N
  have hj : halfJump N 0=N := by simp [halfJump]
  refine ⟨by rw [hb]; norm_num,hl.pow 2,?_,?_,?_,by ring⟩
  · simpa only [neg_sq] using hr.pow 2
  · simpa only [hb,hj,zero_add] using square_derivative_left N 0
  · simpa only [hb,hj,zero_sub,mul_neg,neg_mul] using square_derivative_right N 0

end NField.Alignment.RealBernoulliJumpData
