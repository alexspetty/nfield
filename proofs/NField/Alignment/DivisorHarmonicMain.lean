/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CollisionHarmonicRemainder

/-! # The bounded smooth remainder in the divisor hyperbola formula -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorHarmonicMain
open CollisionHarmonicRemainder

theorem harmonic_with_endpoint {M : ℕ} (hM : 1≤M) :
    (harmonic M : ℝ)=Real.log M+Real.eulerMascheroniConstant+
      1/(2*(M : ℝ))+harmonicError M := by
  have h := (strict_harmonic_remainder hM).1
  have he : M=(M-1)+1 := by omega
  conv_lhs => rw [he,harmonic_succ]
  rw [← he]
  push_cast
  rw [h]
  ring

theorem logarithmic_entropy_bounds {x m : ℝ} (hm : 0<m) (hx : m^2≤x) :
    0≤x*Real.log (x/m^2)-(x-m^2) ∧
      x*Real.log (x/m^2)-(x-m^2)≤(x-m^2)^2/m^2 := by
  have hx0 : 0<x := (sq_pos_of_pos hm).trans_le hx
  have hr : 0<x/m^2 := by positivity
  have hlo := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr) hx0.le
  have hhi := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr) hx0.le
  have he1 : x*(1-(x/m^2)⁻¹)=x-m^2 := by field_simp
  have he2 : x*(x/m^2-1)-(x-m^2)=(x-m^2)^2/m^2 := by field_simp
  rw [he1] at hlo
  constructor
  · linarith
  · linarith

theorem bounded_hyperbola_main {M : ℕ} {x : ℝ} (hM : 1≤M)
    (hlo : (M : ℝ)^2≤x) (hhi : x<((M : ℝ)+1)^2) :
    |2*x*(harmonic M : ℝ)-(M : ℝ)-(M : ℝ)^2-
      (x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x)|≤14 := by
  have hm1 : (1 : ℝ)≤M := by exact_mod_cast hM
  have hm : (0 : ℝ)<M := by linarith
  have hx : 0<x := (sq_pos_of_pos hm).trans_le hlo
  have hm2 : (0 : ℝ)<(M : ℝ)^2 := by positivity
  have he0 : 0≤x-(M : ℝ)^2 := by linarith
  have he3 : x-(M : ℝ)^2≤3*(M : ℝ) := by nlinarith
  have hq := logarithmic_entropy_bounds hm hlo
  have hsquare : (x-(M : ℝ)^2)^2/(M : ℝ)^2≤9 := by
    apply (div_le_iff₀ hm2).mpr
    nlinarith [sq_nonneg (3*(M : ℝ)-(x-(M : ℝ)^2))]
  have hlinear : (x-(M : ℝ)^2)/(M : ℝ)≤3 :=
    (div_le_iff₀ hm).mpr (by linarith)
  have hlinear0 : 0≤(x-(M : ℝ)^2)/(M : ℝ) := by positivity
  have hx4 : x≤4*(M : ℝ)^2 := by nlinarith
  have herr := harmonicError_bounds hM
  have herrorlo : -1≤2*x*harmonicError M := by
    have hb := mul_le_mul_of_nonneg_left herr.1.le (show 0≤2*x by positivity)
    have he : 2*x*-(1/(12*(M : ℝ)^2))= -x/(6*(M : ℝ)^2) := by ring
    rw [he,neg_div] at hb
    have : x/(6*(M : ℝ)^2)≤1 := by
      apply (div_le_iff₀ (by positivity : 0<6*(M : ℝ)^2)).mpr
      nlinarith
    linarith
  have herrorhi : 2*x*harmonicError M≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) herr.2.le
  have hlog : Real.log (x/(M : ℝ)^2)=Real.log x-2*Real.log M := by
    rw [Real.log_div hx.ne' (ne_of_gt hm2),Real.log_pow]
    norm_num
  have he : 2*x*(harmonic M : ℝ)-(M : ℝ)-(M : ℝ)^2-
      (x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x)=
      -(x*Real.log (x/(M : ℝ)^2)-(x-(M : ℝ)^2))+
        (x-(M : ℝ)^2)/(M : ℝ)+2*x*harmonicError M := by
    rw [harmonic_with_endpoint hM,hlog]
    field_simp
    ring
  rw [he,abs_le]
  constructor <;> linarith

end NField.Alignment.DivisorHarmonicMain
