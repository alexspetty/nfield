/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTailBounds

/-!
# Exponential cutoffs below the exact stationary tail height

The floor, logarithmic-square leading coefficient and positive height
margin are proved here before any tail probability estimate is invoked.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionTailCutoffScales

open scoped Classical
open CollisionRemainderDynamics CollisionStationaryAgeAsymptotic

def tailCutoff (d H : ℝ) : ℕ := ⌊Real.exp (d*Real.sqrt H)⌋₊

theorem exp_floor_bounds {z : ℝ} (hz : 4 ≤ z) :
    3 ≤ ⌊Real.exp z⌋₊ ∧ Real.exp z/2 ≤ (⌊Real.exp z⌋₊ : ℝ) ∧
      (⌊Real.exp z⌋₊ : ℝ) ≤ Real.exp z := by
  have he := Real.add_one_le_exp z
  have hf := Nat.lt_floor_add_one (Real.exp z)
  exact ⟨Nat.le_floor (by norm_num; linarith),by linarith,Nat.floor_le (Real.exp_pos z).le⟩

theorem log_exp_floor_le {z : ℝ} (hz : 4 ≤ z) : Real.log (⌊Real.exp z⌋₊ : ℝ) ≤ z := by
  have hb := exp_floor_bounds hz
  have hp : (0 : ℝ) < (⌊Real.exp z⌋₊ : ℕ) := by exact_mod_cast (show 0 < ⌊Real.exp z⌋₊ by omega)
  have hl := Real.log_le_log hp hb.2.2
  rwa [Real.log_exp] at hl

theorem stationaryAge_quadratic_upper : ∃ A : ℝ, 0 ≤ A ∧ ∀ M : ℕ, 3 ≤ M →
    stationaryAge collisionWeight M ≤ (Real.log (M : ℝ))^2/Real.pi^2+A*(1+Real.log M) := by
  let A : ℝ := ((((7+Real.pi^2/6)*momentConstant/2)+2)/3)
  refine ⟨A,by dsimp [A]; positivity [momentConstant_nonneg],?_⟩
  intro M hM
  have h := (le_abs_self (stationaryAge collisionWeight M-(Real.log (M : ℝ))^2/Real.pi^2)).trans
    (stationaryAge_main_error hM)
  change stationaryAge collisionWeight M-(Real.log (M : ℝ))^2/Real.pi^2 ≤ A*(1+Real.log M) at h
  linarith

theorem quadratic_height_margin {q A d X : ℝ} (hq : q < 1) (hA : 0 ≤ A)
    (hX : 1 ≤ X) (hAX : A*(1+d)/((1-q)/2) ≤ X) :
    q*X^2+A*(1+d*X) ≤ (1-(1-q)/2)*X^2 := by
  have hδ : 0 < (1-q)/2 := by linarith
  have ha := (div_le_iff₀ hδ).mp hAX
  have hx0 : 0 ≤ X := by linarith
  have hmul := mul_le_mul_of_nonneg_right ha hx0
  have hlinear := mul_nonneg hA (sub_nonneg.mpr hX)
  nlinarith

theorem tail_cutoff_height {d : ℝ} (hd : 0 < d) (hdπ : d < Real.pi) :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 1 ≤ R ∧ ∀ H : ℝ, R ≤ H →
      4 ≤ d*Real.sqrt H ∧ 3 ≤ tailCutoff d H ∧
      stationaryAge collisionWeight (tailCutoff d H) ≤ (1-δ)*H := by
  obtain ⟨A,hA,hbound⟩ := stationaryAge_quadratic_upper
  let q : ℝ := d^2/Real.pi^2
  have hπ : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hq0 : 0 ≤ q := div_nonneg (sq_nonneg d) hπ.le
  have hq1 : q < 1 := (div_lt_one hπ).mpr (by nlinarith [Real.pi_pos])
  let δ : ℝ := (1-q)/2
  let X0 : ℝ := max 1 (max (4/d) (A*(1+d)/δ))
  have hX01 : 1 ≤ X0 := le_max_left _ _
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ,X0^2,hδ,by dsimp [δ]; linarith,by nlinarith,?_⟩
  intro H hH
  have hH1 : 1 ≤ H := by nlinarith
  have hH0 : 0 ≤ H := by linarith
  have hX0 : X0 ≤ Real.sqrt H := Real.le_sqrt_of_sq_le hH
  have hX1 : 1 ≤ Real.sqrt H := hX01.trans hX0
  have h4d : 4/d ≤ Real.sqrt H := (le_max_left _ _).trans ((le_max_right _ _).trans hX0)
  have h4 : 4 ≤ d*Real.sqrt H := by
    have ht := (div_le_iff₀ hd).mp h4d
    nlinarith
  have hAX : A*(1+d)/δ ≤ Real.sqrt H :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX0)
  have hL3 : 3 ≤ tailCutoff d H := (exp_floor_bounds h4).1
  refine ⟨h4,hL3,?_⟩
  have hLp : (0 : ℝ) < tailCutoff d H := by exact_mod_cast (show 0 < tailCutoff d H by omega)
  have hlog0 : 0 ≤ Real.log (tailCutoff d H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ tailCutoff d H by omega))
  have hlog : Real.log (tailCutoff d H) ≤ d*Real.sqrt H := log_exp_floor_le h4
  have hlogSq : (Real.log (tailCutoff d H))^2 ≤ d^2*H := by
    have hs : (Real.log (tailCutoff d H))^2 ≤ (d*Real.sqrt H)^2 := by
      nlinarith [mul_nonneg hd.le (Real.sqrt_nonneg H)]
    rwa [mul_pow,Real.sq_sqrt hH0] at hs
  have hmain : (Real.log (tailCutoff d H))^2/Real.pi^2 ≤ q*H := by
    calc
      _ ≤ d^2*H/Real.pi^2 := div_le_div_of_nonneg_right hlogSq hπ.le
      _ = _ := by dsimp [q]; ring
  have hlin : A*(1+Real.log (tailCutoff d H)) ≤ A*(1+d*Real.sqrt H) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hA
  have hpar := quadratic_height_margin hq1 hA hX1 hAX
  rw [Real.sq_sqrt hH0] at hpar
  have hage := hbound (tailCutoff d H) hL3
  change q*H+A*(1+d*Real.sqrt H) ≤ (1-δ)*H at hpar
  linarith

end NField.Alignment.CollisionTailCutoffScales
