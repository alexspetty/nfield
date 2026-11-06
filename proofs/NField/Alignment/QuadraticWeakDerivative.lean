/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBoundaryUniformCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv

/-! # Exact integration by parts on every quadratic boundary cell -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.QuadraticWeakDerivative
open scoped BigOperators Topology
open MeasureTheory Set RealBoundaryUniformCells RealBernoulliBoundaryLimits RealBernoulliJumpData

def quadratic (L c x : ℝ) : ℂ := ((L*x+c : ℝ) : ℂ)^2
def quadraticSlope (L c x : ℝ) : ℂ := (2*(L : ℂ))*((L*x+c : ℝ) : ℂ)
def flux (L c : ℝ) (φ φ' : ℝ → ℂ) (x : ℝ) : ℂ :=
  quadratic L c x*φ' x-quadraticSlope L c x*φ x

theorem quadratic_deriv (L c x : ℝ) :
    HasDerivAt (quadratic L c) (quadraticSlope L c x) x := by
  have h := ((((hasDerivAt_id x).const_mul L).add_const c).ofReal_comp).fun_pow 2
  apply h.congr_deriv
  simp [quadraticSlope,mul_assoc,mul_left_comm,mul_comm]

theorem quadratic_slope_deriv (L c x : ℝ) :
    HasDerivAt (quadraticSlope L c) (2*(L : ℂ)^2) x := by
  have h := (((hasDerivAt_id x).const_mul L).add_const c).ofReal_comp.const_mul (2*(L : ℂ))
  apply h.congr_deriv
  simp [pow_two,mul_assoc,mul_left_comm,mul_comm]

theorem quadratic_continuous (L c : ℝ) : Continuous (quadratic L c) := by
  unfold quadratic
  fun_prop

theorem quadratic_slope_continuous (L c : ℝ) : Continuous (quadraticSlope L c) := by
  unfold quadraticSlope
  fun_prop

theorem quadratic_weak_derivative (L c a b : ℝ) (φ φ' φ'' : ℝ → ℂ)
    (hφ : ∀ x,HasDerivAt φ (φ' x) x) (hφ' : ∀ x,HasDerivAt φ' (φ'' x) x)
    (hφ'' : Continuous φ'') :
    (∫ x in a..b,quadratic L c x*φ'' x)=
      2*(L : ℂ)^2*(∫ x in a..b,φ x)+flux L c φ φ' b-flux L c φ φ' a := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hc' : Continuous φ' := continuous_iff_continuousAt.mpr (fun x => (hφ' x).continuousAt)
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (quadratic_continuous L c).continuousOn hc'.continuousOn
    (fun x _ => quadratic_deriv L c x) (fun x _ => hφ' x)
    ((quadratic_slope_continuous L c).intervalIntegrable a b) (hφ''.intervalIntegrable a b)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (quadratic_slope_continuous L c).continuousOn hc.continuousOn
    (fun x _ => quadratic_slope_deriv L c x) (fun x _ => hφ x)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2*(L : ℂ)^2) volume a b)
    (hc'.intervalIntegrable a b)
  rw [h1,h2,intervalIntegral.integral_const_mul]
  unfold flux
  ring

theorem boundary_cell_integrable (N j : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    IntervalIntegrable (fun x => (realBoundary N x : ℂ)^2*g x) volume
      (grid N.factorial j) (grid N.factorial (j+1)) := by
  have hc : IntervalIntegrable (fun x => quadratic (realSlope N) (cellIntercept N j) x*g x) volume
      (grid N.factorial j) (grid N.factorial (j+1)) :=
    ((quadratic_continuous (realSlope N) (cellIntercept N j)).mul hg).intervalIntegrable _ _
  apply hc.congr_uIoo
  intro x hx
  rw [uIoo_of_le (grid_step (Nat.factorial_pos N) j).le] at hx
  dsimp only
  rw [boundary_on_cell N j hx]
  rfl

theorem boundary_cell_weak_derivative (N j : ℕ) (φ φ' φ'' : ℝ → ℂ)
    (hφ : ∀ x,HasDerivAt φ (φ' x) x) (hφ' : ∀ x,HasDerivAt φ' (φ'' x) x)
    (hφ'' : Continuous φ'') :
    (∫ x in grid N.factorial j..grid N.factorial (j+1),(realBoundary N x : ℂ)^2*φ'' x)=
      2*(realSlope N : ℂ)^2*(∫ x in grid N.factorial j..grid N.factorial (j+1),φ x)+
        flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial (j+1))-
        flux (realSlope N) (cellIntercept N j) φ φ' (grid N.factorial j) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (grid_step (Nat.factorial_pos N) j).le
    (g := fun x => quadratic (realSlope N) (cellIntercept N j) x*φ'' x)
    (by intro x hx; dsimp only; rw [boundary_on_cell N j hx]; rfl)]
  exact quadratic_weak_derivative _ _ _ _ φ φ' φ'' hφ hφ' hφ''

end NField.Alignment.QuadraticWeakDerivative
