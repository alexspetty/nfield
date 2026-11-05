/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRootSumBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The manuscript's logarithmic prime cutoff and return horizon

For t = 1/epsilon these are exactly floor(t log(t)/10) and floor(P/4).
The explicit threshold exp(40) is only an auxiliary proof constant.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConcentrationScales

def primeScale (t : ℝ) : ℕ := ⌊t*Real.log t/10⌋₊

def returnScale (t : ℝ) : ℕ := primeScale t/4

theorem primeScale_reciprocal {ε : ℝ} (hε : 0<ε) :
    primeScale (1/ε)=⌊Real.log (1/ε)/(10*ε)⌋₊ := by
  unfold primeScale
  congr 1
  field_simp

theorem scale_threshold {t : ℝ} (ht : Real.exp 40≤t) : 41≤t ∧ 40≤Real.log t := by
  have hp : 0<t := (Real.exp_pos 40).trans_le ht
  exact ⟨by linarith [Real.add_one_le_exp (40 : ℝ)],(Real.le_log_iff_exp_le hp).mpr ht⟩

theorem primeScale_bounds {t : ℝ} (ht : Real.exp 40≤t) :
    t*Real.log t/20≤(primeScale t : ℝ) ∧ (primeScale t : ℝ)≤t*Real.log t/10 := by
  obtain ⟨ht41,hl40⟩ := scale_threshold ht
  have hx : 0≤t*Real.log t/10 := by positivity
  have hlo := Nat.lt_floor_add_one (t*Real.log t/10)
  change t*Real.log t/10<(primeScale t : ℝ)+1 at hlo
  exact ⟨by nlinarith, Nat.floor_le hx⟩

theorem primeScale_twice {t : ℝ} (ht : Real.exp 40≤t) : 2*t≤(primeScale t : ℝ) := by
  obtain ⟨ht41,hl40⟩ := scale_threshold ht
  have hp := (primeScale_bounds ht).1
  nlinarith

theorem primeScale_pos {t : ℝ} (ht : Real.exp 40≤t) : (0 : ℝ)<primeScale t := by
  have hp := primeScale_twice ht
  have h41 := (scale_threshold ht).1
  linarith

theorem primeScale_log_lower {t : ℝ} (ht : Real.exp 40≤t) : 1≤Real.log (primeScale t) := by
  obtain ⟨ht41,hl40⟩ := scale_threshold ht
  have hp := primeScale_twice ht
  have hl := Real.log_le_log (by linarith : 0<t) (show t≤(primeScale t : ℝ) by linarith)
  linarith

theorem primeScale_width {t : ℝ} (ht : Real.exp 40≤t) :
    3/t<Real.log ((primeScale t : ℝ)/2)/(primeScale t : ℝ) := by
  have ht0 : 0<t := (Real.exp_pos 40).trans_le ht
  have hp0 := primeScale_pos ht
  have hp := primeScale_twice ht
  have hl : Real.log t≤Real.log ((primeScale t : ℝ)/2) :=
    Real.log_le_log ht0 (by linarith)
  have hr : 10/t≤Real.log t/(primeScale t : ℝ) := by
    apply (div_le_div_iff₀ ht0 hp0).mpr
    have hhi := (primeScale_bounds ht).2
    nlinarith
  calc
    _ < 10/t := div_lt_div_of_pos_right (by norm_num) ht0
    _ ≤ Real.log t/(primeScale t : ℝ) := hr
    _ ≤ _ := div_le_div_of_nonneg_right hl hp0.le

theorem returnScale_floor (t : ℝ) :
    returnScale t=⌊(primeScale t : ℝ)/4⌋₊ := by
  exact (Nat.floor_div_eq_div (K := ℝ) (primeScale t) 4).symm

theorem returnScale_upper (t : ℝ) : 4*returnScale t≤primeScale t := by
  simpa only [returnScale,Nat.mul_comm] using Nat.div_mul_le_self (primeScale t) 4

theorem returnScale_lower {t : ℝ} (ht : Real.exp 40≤t) :
    (primeScale t : ℝ)/8≤(returnScale t : ℝ) ∧ t*Real.log t/160≤(returnScale t : ℝ) := by
  have hp := primeScale_twice ht
  have h41 := (scale_threshold ht).1
  have hf := Nat.lt_floor_add_one ((primeScale t : ℝ)/4)
  rw [← returnScale_floor] at hf
  have hlo : (primeScale t : ℝ)/8≤(returnScale t : ℝ) := by linarith
  exact ⟨hlo,by have hb := (primeScale_bounds ht).1; linarith⟩

theorem returnScale_pos {t : ℝ} (ht : Real.exp 40≤t) : 0<returnScale t := by
  have hp := primeScale_pos ht
  have hn := (returnScale_lower ht).1
  have h : (0 : ℝ)<returnScale t := by linarith
  exact_mod_cast h

theorem primeScale_log_upper {t : ℝ} (ht : Real.exp 40≤t) :
    Real.log (primeScale t)≤2*Real.log t := by
  have ht0 : 0<t := (Real.exp_pos 40).trans_le ht
  have hb := (primeScale_bounds ht).2
  have hlog := Real.log_le_self ht0.le
  have hpsq : (primeScale t : ℝ)≤t^2 := by nlinarith [sq_nonneg t]
  have hl := Real.log_le_log (primeScale_pos ht) hpsq
  simpa only [Real.log_pow,Nat.cast_ofNat] using hl

theorem scale_ratio_bound {t : ℝ} (ht : Real.exp 40≤t) :
    Real.log (primeScale t)/(returnScale t : ℝ)≤320/t := by
  have ht0 : 0<t := (Real.exp_pos 40).trans_le ht
  have hn : (0 : ℝ)<returnScale t := by exact_mod_cast returnScale_pos ht
  apply (div_le_div_iff₀ hn ht0).mpr
  have hlo := (returnScale_lower ht).2
  have hhi := mul_le_mul_of_nonneg_left (primeScale_log_upper ht) ht0.le
  nlinarith

end NField.Alignment.CollisionConcentrationScales
