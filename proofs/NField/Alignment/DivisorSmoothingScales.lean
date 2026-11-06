/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalSmoothingCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The actual cubic-root scale satisfies every smoothing constraint eventually -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorSmoothingScales
open scoped Topology
open Filter Asymptotics

theorem cubic_root_cube {x : ℝ} (hx : 0≤x) : (x^(1/3 : ℝ))^3=x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

theorem cubic_root_square {x : ℝ} (hx : 0≤x) : (x^(1/3 : ℝ))^2=x^(2/3 : ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

theorem sqrt_sixth_root {x : ℝ} (hx : 0<x) :
    Real.sqrt x*x^(1/6 : ℝ)=(x^(1/3 : ℝ))^2 := by
  rw [cubic_root_square hx.le,Real.sqrt_eq_rpow,← Real.rpow_add hx]
  congr 1
  norm_num

theorem eventual_smoothing_scale : ∀ᶠ x : ℝ in atTop,
    1≤x ∧ 1≤x^(1/3 : ℝ) ∧
      Real.sqrt x*(2+Real.log x)^3≤(x^(1/3 : ℝ))^2 := by
  have hb := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ)<1/6)).bound (by norm_num : (0 : ℝ)<1/27)
  filter_upwards [hb,eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hb hx hlog
  have hx0 : 0<x := by linarith
  have hl0 : 0≤Real.log x := by linarith
  simp only [Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤Real.log x^3),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (1/6 : ℝ))] at hb
  have hcube : (2+Real.log x)^3≤27*Real.log x^3 := by
    calc
      _ ≤ (3*Real.log x)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by ring
  refine ⟨hx,Real.one_le_rpow hx (by norm_num),?_⟩
  calc
    _ ≤ Real.sqrt x*(27*Real.log x^3) := mul_le_mul_of_nonneg_left hcube (Real.sqrt_nonneg x)
    _ ≤ Real.sqrt x*x^(1/6 : ℝ) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg x)
    _ = _ := sqrt_sixth_root hx0

end NField.Alignment.DivisorSmoothingScales
