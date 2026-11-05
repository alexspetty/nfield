/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentGlobalEnvelope
import NField.Alignment.CollisionLogLogEnvelopes
import NField.Alignment.CollisionLcmSharpOrders

/-!
# The sharp upper alignment order for every modulus

The absent-prime multiplier tends to one, and its logarithmic tail is
eventually at most one. Both errors are retained in the global estimate
before the sharp Gamma coefficient is obtained.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentSharpUpper

open Filter Asymptotics CollisionAlignmentGlobalEnvelope CollisionLogLogEnvelopes
open CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum CollisionLimitingPrimeProduct
open CollisionLimitingPrimeLogSum CollisionLcmSharpOrders CollisionZetaMoments CollisionCylinderMeans

def alignmentGlobalUpper (L : ℕ) : ℝ :=
  primeEulerEnvelope (|Real.eulerMascheroniConstant|+3) 0 (Real.log L)*
    (1+4/Real.log L)/3+(zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant+1|)/3

theorem absent_log_envelope_tendsto :
    Tendsto (fun y : ℝ => 2*(2*Real.log y+3)/y) atTop (nhds 0) := by
  have hl : Tendsto (fun y : ℝ => Real.log y/y) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have he (y : ℝ) : 2*(2*Real.log y+3)/y=4*(Real.log y/y)+6*y⁻¹ := by ring
  simp_rw [he]
  simpa only [mul_zero,add_zero] using (hl.const_mul 4).add (hi.const_mul 6)

theorem alignment_global_upper {L : ℕ} (hL : 0 < L) (hlog : 2 ≤ Real.log L)
    (htail : 2*(2*Real.log (Real.log L)+3)/Real.log L ≤ 1) :
    alignmentConstant L ≤ alignmentGlobalUpper L := by
  have hlog0 : Real.log (L : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have he : Real.log (L : ℝ)/(Real.log L*Real.log (Real.log L))=1/Real.log (Real.log L) := by
    field_simp
  have hP := alignmentEulerProduct_global_bound hL hlog
  rw [he] at hP
  have hS : alignmentEulerLogSum L ≤ limitingPrimeLogSum (Real.log L)+3 := by
    have h := alignmentEulerLogSum_global_bound hL hlog
    rw [mul_div_cancel_right₀ _ hlog0] at h
    linarith
  have hB : 0 ≤ |Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log L)+3 := by
    have h := (alignmentEulerLogSum_nonneg L).trans hS
    linarith [abs_nonneg Real.eulerMascheroniConstant]
  have hmain : alignmentEulerProduct L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L) ≤
      (limitingPrimeProduct (Real.log L)*Real.exp (1/Real.log (Real.log L))*(1+4/Real.log L))*
        (|Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log L)+3) := by
    calc
      _ ≤ alignmentEulerProduct L*(|Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log L)+3) :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self Real.eulerMascheroniConstant])
          (alignmentEulerProduct_nonneg L)
      _ ≤ _ := mul_le_mul_of_nonneg_right hP hB
  have herr := (le_abs_self _).trans (alignment_euler_scaled_error hL)
  unfold alignmentGlobalUpper primeEulerEnvelope
  nlinarith

theorem alignment_eventual_upper :
    ∀ᶠ L : ℕ in atTop, alignmentConstant L ≤ alignmentGlobalUpper L := by
  have ht := (absent_log_envelope_tendsto.comp log_nat_tendsto_atTop).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_gt_atTop (0 : ℕ),log_nat_tendsto_atTop.eventually_ge_atTop 2,ht]
    with L hL hlog htail
  exact alignment_global_upper hL hlog htail.le

theorem absent_product_log_multiplier_tendsto :
    Tendsto (fun L : ℕ => 1+4/Real.log L) atTop (nhds 1) := by
  have h : Tendsto (fun L : ℕ => (Real.log L)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp log_nat_tendsto_atTop
  simpa only [div_eq_mul_inv,mul_zero,add_zero] using (h.const_mul 4).const_add 1

theorem alignmentGlobalUpper_asymptotic :
    alignmentGlobalUpper ~[atTop] (fun L : ℕ => alignmentGamma*(Real.log (Real.log L))^2) := by
  have hm : (fun L : ℕ => 1+4/Real.log L) ~[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isEquivalent_const_iff_tendsto (by norm_num : (1 : ℝ) ≠ 0)).mpr
      absent_product_log_multiplier_tendsto
  have h3 : (fun _ : ℕ => (3 : ℝ)) ~[atTop] (fun _ : ℕ => (3 : ℝ)) := IsEquivalent.refl
  have hmain : (fun L : ℕ => primeEulerEnvelope (|Real.eulerMascheroniConstant|+3) 0 (Real.log L)*
      (1+4/Real.log L)/3) ~[atTop]
      (fun L : ℕ => alignmentGamma*(Real.log (Real.log L))^2) := by
    have h := ((primeEulerEnvelope_log_nat_asymptotic (|Real.eulerMascheroniConstant|+3) 0).mul hm).div h3
    convert! h using 1
    funext L
    dsimp only [Pi.mul_apply,Pi.div_apply]
    unfold alignmentGamma
    ring
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun L : ℕ => (Real.log (Real.log L))^2) := by
    simpa using ((constant_isLittleO_log 1).comp_tendsto log_nat_tendsto_atTop).pow
      (by norm_num : 0 < (2 : ℕ))
  have hE : (fun _ : ℕ => (zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant+1|)/3)
      =o[atTop] (fun L : ℕ => alignmentGamma*(Real.log (Real.log L))^2) := by
    simpa only [mul_one] using (h1.const_mul_left
      ((zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant+1|)/3)).const_mul_right alignmentGamma_pos.ne'
  exact hmain.add_isLittleO hE

theorem alignment_sharp_upper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ L : ℕ in atTop, alignmentConstant L ≤
      (alignmentGamma+epsilon)*(Real.log (Real.log L))^2 := by
  have herror := isLittleO_iff.mp alignmentGlobalUpper_asymptotic.isLittleO
    (div_pos hepsilon alignmentGamma_pos)
  have he : (epsilon/alignmentGamma)*alignmentGamma=epsilon :=
    div_mul_cancel₀ epsilon alignmentGamma_pos.ne'
  filter_upwards [alignment_eventual_upper,herror] with L hL herr
  change ‖alignmentGlobalUpper L-alignmentGamma*(Real.log (Real.log L))^2‖ ≤
    (epsilon/alignmentGamma)*‖alignmentGamma*(Real.log (Real.log L))^2‖ at herr
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg alignmentGamma_pos.le (sq_nonneg _)),
    ← mul_assoc,he] at herr
  have h := (le_abs_self _).trans herr
  nlinarith

end NField.Alignment.CollisionAlignmentSharpUpper
