/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BoundaryJumpFlux

/-! # The distributional second derivative of the actual squared boundary -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BoundaryDistributionalDerivative
open scoped BigOperators Topology
open MeasureTheory RealBernoulliBoundaryLimits RealBernoulliJumpData RealBoundaryUniformCells
  QuadraticWeakDerivative BoundaryJumpFlux

theorem boundary_integral_partition (N : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    (∑ j ∈ Finset.range N.factorial,
      ∫ x in grid N.factorial j..grid N.factorial (j+1),(realBoundary N x : ℂ)^2*g x)=
      ∫ x in (0 : ℝ)..1,(realBoundary N x : ℂ)^2*g x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (fun j (_ : j<N.factorial) => boundary_cell_integrable N j g hg)
  have hD : (N.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
  simpa only [grid,Nat.cast_zero,zero_div,div_self hD] using h

theorem continuous_integral_partition (N : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    (∑ j ∈ Finset.range N.factorial,
      ∫ x in grid N.factorial j..grid N.factorial (j+1),g x)=∫ x in (0 : ℝ)..1,g x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := grid N.factorial) (n := N.factorial)
    (fun j _ => hg.intervalIntegrable (grid N.factorial j) (grid N.factorial (j+1)))
  have hD : (N.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
  simpa only [grid,Nat.cast_zero,zero_div,div_self hD] using h

/-- Title: `Distributional second derivative of the squared boundary`.
The Dirac derivative is evaluated as minus the first derivative of the test function.
The finite grid contains every jump; its extra points have zero jump data. -/
theorem boundary_distributional_second_derivative (N : ℕ) (φ φ' φ'' : ℝ → ℂ)
    (hφ : ∀ x,HasDerivAt φ (φ' x) x) (hφ' : ∀ x,HasDerivAt φ' (φ'' x) x)
    (hφ'' : Continuous φ'') (hperiod : φ 1=φ 0) (hperiod' : φ' 1=φ' 0) :
    (∫ x in (0 : ℝ)..1,(realBoundary N x : ℂ)^2*φ'' x)=
      2*(realSlope N : ℂ)^2*(∫ x in (0 : ℝ)..1,φ x)+
      ∑ j ∈ Finset.range N.factorial,
        ((slopeJump N (grid N.factorial j) : ℂ)*φ (grid N.factorial j)-
         (valueJump N (grid N.factorial j) : ℂ)*φ' (grid N.factorial j)) := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hcell (j : ℕ) :
      (∫ x in grid N.factorial j..grid N.factorial (j+1),(realBoundary N x : ℂ)^2*φ'' x)=
      2*(realSlope N : ℂ)^2*(∫ x in grid N.factorial j..grid N.factorial (j+1),φ x)+
      (flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial (j+1))-
       flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial j)) := by
    rw [boundary_cell_weak_derivative N j φ φ' φ'' hφ hφ' hφ'']
    ring
  rw [← boundary_integral_partition N φ'' hφ'']
  simp_rw [hcell]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,continuous_integral_partition N φ hc,
    cell_flux_sum N φ φ' hperiod hperiod']

end NField.Alignment.BoundaryDistributionalDerivative
