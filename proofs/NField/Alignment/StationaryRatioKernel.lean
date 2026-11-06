/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryWeightConstants
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # An inverse-linear tail bound for the translated logarithmic polynomial -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryRatioKernel
open Filter MeasureTheory Set CollisionLogTailKernel

def ratioKernel (M x : ℝ) : ℝ := (1 + Real.log x - Real.log M) ^ 2 / x ^ 2
def ratioTail (M x : ℝ) : ℝ :=
  ((Real.log x - Real.log M) ^ 2 + 4 * (Real.log x - Real.log M) + 5) / x

theorem ratioKernel_nonneg (M x : ℝ) : 0 ≤ ratioKernel M x := by unfold ratioKernel; positivity

theorem ratioKernel_hasDerivAt (M : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ratioKernel M)
      (-2 * (1 + Real.log x - Real.log M) * (Real.log x - Real.log M) / x ^ 3) x := by
  have hd := ((((Real.hasDerivAt_log hx).const_add 1).sub_const (Real.log M)).pow 2).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  convert! hd using 1
  dsimp
  field_simp
  ring

theorem ratioTail_hasDerivAt (M : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ratioTail M) (-ratioKernel M x) x := by
  have hL := (Real.hasDerivAt_log hx).sub_const (Real.log M)
  have hd := (((hL.pow 2).add (hL.const_mul 4)).add_const 5).div (hasDerivAt_id x) hx
  convert! hd using 1
  dsimp [ratioKernel]
  field_simp
  ring

theorem ratioTail_tendsto_zero (M : ℝ) : Tendsto (ratioTail M) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => (Real.log M ^ 2 - 4 * Real.log M + 5) / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hs := ((logPower_div_linear_tendsto 2).add
    ((logPower_div_linear_tendsto 1).const_mul (4 - 2 * Real.log M))).add h0
  norm_num only [mul_zero, zero_add] at hs
  convert! hs using 1
  funext x
  unfold ratioTail
  simp only [pow_one]
  ring

theorem negative_ratioTail_hasDerivAt (M : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => -ratioTail M x) (ratioKernel M x) x := by
  have h := (ratioTail_hasDerivAt M hx).neg
  simp only [neg_neg] at h
  convert! h using 1

theorem ratioKernel_integrable {M : ℝ} (hM : 0 < M) :
    IntegrableOn (ratioKernel M) (Ioi M) := by
  have ht := (ratioTail_tendsto_zero M).neg
  simp only [neg_zero] at ht
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => negative_ratioTail_hasDerivAt M (ne_of_gt (hM.trans_le hx)))
    (fun x _ => ratioKernel_nonneg M x) ht

theorem ratioKernel_integral {M : ℝ} (hM : 0 < M) :
    (∫ x in Ioi M, ratioKernel M x) = 5 / M := by
  have ht := (ratioTail_tendsto_zero M).neg
  simp only [neg_zero] at ht
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => negative_ratioTail_hasDerivAt M (ne_of_gt (hM.trans_le hx)))
    (fun x _ => ratioKernel_nonneg M x) ht
  simpa [ratioTail] using h

theorem ratioKernel_antitone {M : ℝ} (hM : 0 < M) :
    AntitoneOn (ratioKernel M) (Ici M) := by
  have hd : ∀ x ∈ Ici M, HasDerivAt (ratioKernel M)
      (-2 * (1 + Real.log x - Real.log M) * (Real.log x - Real.log M) / x ^ 3) x :=
    fun x hx => ratioKernel_hasDerivAt M (ne_of_gt (hM.trans_le hx))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hMx : M ≤ x := interior_subset hx
  have hl : 0 ≤ Real.log x - Real.log M := sub_nonneg.mpr (Real.log_le_log hM hMx)
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)) hl
  · exact (pow_pos (hM.trans_le hMx) 3).le

/-- Title: `The translated quadratic logarithm has an inverse-linear tail`. -/
theorem ratio_kernel_tail_bound {M : ℕ} (hM : 1 ≤ M) :
    (∑' j : ℕ, ratioKernel M (j + M + 1 : ℕ)) ≤ 5 / (M : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h := (ratioKernel_antitone hM0).tsum_comp_add_le_integral M
    (ratioKernel_integrable hM0) (fun x _ => ratioKernel_nonneg M x)
  rwa [ratioKernel_integral hM0] at h

theorem ratio_kernel_tail_summable {M : ℕ} (hM : 1 ≤ M) :
    Summable (fun j : ℕ => ratioKernel M (j + M + 1 : ℕ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs := (ratioKernel_antitone hM0).summable_of_integrableOn_Ioi
    (ratioKernel_integrable hM0) (fun x _ => ratioKernel_nonneg M x)
  exact hs.comp_injective (fun _ _ h => by omega)

end NField.Alignment.StationaryRatioKernel
