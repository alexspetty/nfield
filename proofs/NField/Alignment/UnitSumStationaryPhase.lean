/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SquareZeroUnitShift
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Exact stationary-phase filtering by square-zero translations

Average permutations of the actual unit set. Primitive character
orthogonality removes precisely the nonstationary units. This identity
retains arbitrary phase parameters and supplies a count bound, without
assuming any bound for the critical congruence.
-/

set_option autoImplicit false
namespace NField.Alignment.UnitSumStationaryPhase
open scoped BigOperators Classical
open SquareZeroUnitShift
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- The literal unit exponential sum with both inverse-additive parameters. -/
noncomputable def unitSum (ψ : AddChar R ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, ψ (phase a b u)

/-- Translation by c*t is an actual unit permutation when c squared is zero. -/
theorem sum_shift (ψ : AddChar R ℂ) (a b c : R) (hc : c^2=0) (t : R) :
    unitSum ψ a b = ∑ u : Rˣ, ψ (phase a b u)*ψ (t*(c*(a-b*((u⁻¹:Rˣ):R)^2))) := by
  have hd : (c*t)^2=0 := by rw [mul_pow,hc,zero_mul]
  unfold unitSum
  rw [← (shiftEquiv (c*t) hd).sum_comp (fun u : Rˣ => ψ (phase a b u))]
  apply Finset.sum_congr rfl
  intro u _
  rw [shiftEquiv_apply,phase_shift,AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Averaging the exact translation identity over all ring elements. -/
theorem averaged_sum (ψ : AddChar R ℂ) (a b c : R) (hc : c^2=0) :
    (Fintype.card R:ℂ)*unitSum ψ a b =
      ∑ u : Rˣ, ψ (phase a b u)*∑ t : R, ψ (t*(c*(a-b*((u⁻¹:Rˣ):R)^2))) := by
  calc
    _ = ∑ _t : R, unitSum ψ a b := by simp
    _ = ∑ t : R, ∑ u : Rˣ, ψ (phase a b u)*ψ (t*(c*(a-b*((u⁻¹:Rˣ):R)^2))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact sum_shift ψ a b c hc t
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

/-- Primitive additive orthogonality gives the exact stationary filter.
The critical equation is cleared using the square of an actual unit. -/
theorem sum_eq_critical (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) :
    unitSum ψ a b = ∑ u : Rˣ, if c*(a*(u:R)^2-b)=0 then ψ (phase a b u) else 0 := by
  have h := averaged_sum ψ a b c hc
  have hcard : (Fintype.card R:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [h]
  simp_rw [AddChar.sum_mulShift _ hψ,critical_iff]
  simp [Finset.mul_sum,mul_ite,ite_mul,mul_comm]

/-- Only stationary units can contribute; each retained summand has norm one. -/
theorem norm_le_critical_count (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) :
    ‖unitSum ψ a b‖ ≤
      ((Finset.univ.filter (fun u : Rˣ => c*(a*(u:R)^2-b)=0)).card:ℝ) := by
  rw [sum_eq_critical ψ hψ a b c hc]
  calc
    _ ≤ ∑ u : Rˣ, ‖if c*(a*(u:R)^2-b)=0 then ψ (phase a b u) else (0:ℂ)‖ := norm_sum_le _ _
    _ = _ := by simp [apply_ite norm,AddChar.norm_apply]

/-- Absence of critical units makes the literal exponential sum zero. -/
theorem sum_eq_zero_of_no_critical (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) (hcrit : ∀ u : Rˣ, c*(a*(u:R)^2-b)≠0) :
    unitSum ψ a b = 0 := by
  rw [sum_eq_critical ψ hψ a b c hc]
  apply Finset.sum_eq_zero
  intro u _
  exact if_neg (hcrit u)

end NField.Alignment.UnitSumStationaryPhase
