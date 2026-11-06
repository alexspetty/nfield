/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.KorolevRealCutoff

/-! # The actual short-range logarithmic cost is little-o of the inverse harmonic scale -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevShortRangeAsymptotic
open scoped Topology
open Filter Asymptotics DedekindInverseResidueTransform

theorem logarithm_lower_range (q : ℕ) :
    Real.log (korolevLowerRange q)=
      Real.log (q : ℝ)^(4/5 : ℝ)*Real.log (Real.log (q : ℝ))^(73/5 : ℝ) := by
  simp [korolevLowerRange]

/-- Title: `The printed short-range cost is negligible at the inverse harmonic scale`. -/
theorem short_range_isLittleO :
    (fun q => Real.log (korolevLowerRange q)) =o[atTop]
      (fun q => Real.log (q : ℝ)/Real.log (Real.log (q : ℝ))) := by
  have hl : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hv := Real.tendsto_log_atTop.comp hl
  have hpos : ∀ᶠ q : ℕ in atTop,0<Real.log (q : ℝ) ∧ 0<Real.log (Real.log (q : ℝ)) := by
    filter_upwards [hl.eventually_gt_atTop 0,hv.eventually_gt_atTop 0] with q hq hq'
    exact ⟨hq,hq'⟩
  apply (isLittleO_iff_tendsto' (hpos.mono (fun q hq hz =>
    (div_ne_zero hq.1.ne' hq.2.ne' hz).elim))).mpr
  have ht := ((isLittleO_log_rpow_rpow_atTop (78/5 : ℝ)
    (by norm_num : (0 : ℝ)<1/5)).comp_tendsto hl).tendsto_div_nhds_zero
  apply ht.congr'
  filter_upwards [hpos] with q hq
  dsimp only [Function.comp_apply]
  rw [logarithm_lower_range]
  have hL : Real.log (q : ℝ)^(4/5 : ℝ)*Real.log (q : ℝ)^(1/5 : ℝ)=Real.log (q : ℝ) := by
    rw [← Real.rpow_add hq.1]
    norm_num
  have hV : Real.log (Real.log (q : ℝ))^(73/5 : ℝ)*Real.log (Real.log (q : ℝ))=
      Real.log (Real.log (q : ℝ))^(78/5 : ℝ) := by
    nth_rw 2 [← Real.rpow_one (Real.log (Real.log (q : ℝ)))]
    rw [← Real.rpow_add hq.2]
    norm_num
  have hpow : Real.log (q : ℝ)^(4/5 : ℝ)≠0 := (Real.rpow_pos_of_pos hq.1 _).ne'
  rw [← hV]
  field_simp [hq.1.ne',hq.2.ne',hpow]
  linear_combination -(Real.log (Real.log (q : ℝ)))^(73/5 : ℝ)*hL

end NField.Alignment.KorolevShortRangeAsymptotic
