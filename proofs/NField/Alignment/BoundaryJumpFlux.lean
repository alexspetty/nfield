/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.QuadraticWeakDerivative

/-! # The exact boundary flux and finite cyclic jump ledger -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BoundaryJumpFlux
open scoped BigOperators Topology
open RealBernoulliBoundaryLimits RealBernoulliJumpData RealBoundaryUniformCells QuadraticWeakDerivative

def valueJump (N : ℕ) (x : ℝ) : ℝ := -4*(halfJump N x : ℝ)*realBoundary N x
def slopeJump (N : ℕ) (x : ℝ) : ℝ := -4*realSlope N*(halfJump N x : ℝ)
def leftFlux (N : ℕ) (φ φ' : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((realBoundary N x-(halfJump N x : ℝ) : ℝ) : ℂ)^2)*φ' x-
    (2*(realSlope N : ℂ))*((realBoundary N x-(halfJump N x : ℝ) : ℝ) : ℂ)*φ x
def rightFlux (N : ℕ) (φ φ' : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((realBoundary N x+(halfJump N x : ℝ) : ℝ) : ℂ)^2)*φ' x-
    (2*(realSlope N : ℂ))*((realBoundary N x+(halfJump N x : ℝ) : ℝ) : ℂ)*φ x

theorem actual_square_jump (N : ℕ) (x : ℝ) :
    (realBoundary N x-(halfJump N x : ℝ))^2-
      (realBoundary N x+(halfJump N x : ℝ))^2=valueJump N x := by
  unfold valueJump
  ring

theorem actual_slope_jump (N : ℕ) (x : ℝ) :
    2*realSlope N*(realBoundary N x-(halfJump N x : ℝ))-
      2*realSlope N*(realBoundary N x+(halfJump N x : ℝ))=slopeJump N x := by
  unfold slopeJump
  ring

theorem flux_jump (N : ℕ) (φ φ' : ℝ → ℂ) (x : ℝ) :
    rightFlux N φ φ' x-leftFlux N φ φ' x=
      (slopeJump N x : ℂ)*φ x-(valueJump N x : ℂ)*φ' x := by
  unfold rightFlux leftFlux slopeJump valueJump
  push_cast
  ring

theorem cell_left_flux (N j : ℕ) (φ φ' : ℝ → ℂ) :
    flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial j)=
      leftFlux N φ φ' (grid N.factorial j) := by
  unfold flux quadratic quadraticSlope
  change (cellBoundary N j (grid N.factorial j) : ℂ)^2*φ' (grid N.factorial j)-
    (2*(realSlope N : ℂ))*(cellBoundary N j (grid N.factorial j) : ℂ)*φ (grid N.factorial j)=_
  rw [cell_left_endpoint]
  rfl

theorem cell_right_flux (N j : ℕ) (φ φ' : ℝ → ℂ) :
    flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial (j+1))=
      rightFlux N φ φ' (grid N.factorial (j+1)) := by
  unfold flux quadratic quadraticSlope
  change (cellBoundary N j (grid N.factorial (j+1)) : ℂ)^2*φ' (grid N.factorial (j+1))-
    (2*(realSlope N : ℂ))*(cellBoundary N j (grid N.factorial (j+1)) : ℂ)*φ (grid N.factorial (j+1))=_
  rw [cell_right_endpoint]
  rfl

theorem right_flux_period_endpoint (N : ℕ) (φ φ' : ℝ → ℂ)
    (hφ : φ 1=φ 0) (hφ' : φ' 1=φ' 0) : rightFlux N φ φ' 1=rightFlux N φ φ' 0 := by
  simp [rightFlux,realBoundary,halfJump,CollisionDedekindPairing.periodicSawtooth,hφ,hφ']

theorem cyclic_shift_sum {A : Type*} [AddCommGroup A] (f : ℕ → A) (D : ℕ) (hD : f D=f 0) :
    (∑ j ∈ Finset.range D,f (j+1))=∑ j ∈ Finset.range D,f j := by
  have h := (Finset.sum_range_succ' f D).symm.trans (Finset.sum_range_succ f D)
  rw [hD] at h
  exact add_right_cancel h

theorem cell_flux_sum (N : ℕ) (φ φ' : ℝ → ℂ)
    (hφ : φ 1=φ 0) (hφ' : φ' 1=φ' 0) :
    (∑ j ∈ Finset.range N.factorial,
      (flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial (j+1))-
       flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial j)))=
    ∑ j ∈ Finset.range N.factorial,
      ((slopeJump N (grid N.factorial j) : ℂ)*φ (grid N.factorial j)-
       (valueJump N (grid N.factorial j) : ℂ)*φ' (grid N.factorial j)) := by
  simp_rw [cell_left_flux,cell_right_flux]
  rw [Finset.sum_sub_distrib]
  have hend : rightFlux N φ φ' (grid N.factorial N.factorial)=rightFlux N φ φ' (grid N.factorial 0) := by
    have hD : (N.factorial : ℝ)≠0 := by exact_mod_cast (Nat.factorial_ne_zero N)
    simpa only [grid,div_self hD,Nat.cast_zero,zero_div] using right_flux_period_endpoint N φ φ' hφ hφ'
  rw [cyclic_shift_sum (fun j => rightFlux N φ φ' (grid N.factorial j)) N.factorial hend,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => flux_jump N φ φ' (grid N.factorial j))

end NField.Alignment.BoundaryJumpFlux
