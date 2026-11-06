/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourcePrefixBound

/-! # The published inverse-fraction range estimate from the actual source decomposition -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevRangeEstimate
open Filter KorolevSourceWindowCount KorolevSourceScales
  DedekindInverseResidueTransform
open scoped Topology

def coordinateDecay (v u : ℝ) : ℝ :=
  Real.exp (-5*u/24+v/6+49*Real.log v/24)

/-- The manuscript's exact decay factor in logarithmic source coordinates. -/
theorem decay_coordinates {m X : ℕ} (hL : 0 < Real.log (m : ℝ))
    (hX : 0 < Real.log (X : ℝ)) (hv : 0 < Real.log (Real.log m)) :
    korolevPrefixDecay m X =
      coordinateDecay (Real.log (Real.log m)) (Real.log (Real.log X)) := by
  unfold korolevPrefixDecay coordinateDecay
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hv,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The source-gamma error fits the published decay without a Fourier completion factor. -/
theorem gamma_error_le {v u c : ℝ} (hv : 1 ≤ v) (hu : u ≤ v) :
    u*Real.exp (-gain v u c) ≤ Real.exp (c/24)*coordinateDecay v u := by
  have hv0 : 0 < v := by linarith
  have hpow : Real.exp (2*Real.log v) = v^2 := by
    rw [show (2 : ℝ)*Real.log v = (2 : ℕ)*Real.log v by norm_num,
      Real.exp_nat_mul, Real.exp_log hv0]
  have hid : Real.exp (c/24)*coordinateDecay v u = v^2*Real.exp (-gain v u c) := by
    unfold coordinateDecay
    rw [← hpow, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold gain
    ring
  rw [hid]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith

/-- The canonical X/log m term also fits the published decay. -/
theorem inverse_exp_le_decay {v u : ℝ} (hv : 1 ≤ v) (hu : u ≤ v) :
    1/Real.exp v ≤ coordinateDecay v u := by
  rw [one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log v := Real.log_nonneg hv
  linarith

/-- The published lower range is contained in the source decomposition's lower range. -/
theorem source_lower_le_published {m : ℕ} (hv : 1 ≤ Real.log (Real.log m)) :
    Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ korolevLowerRange m := by
  unfold korolevLowerRange
  simp only [Real.rpow_eq_pow]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.log_natCast_nonneg m) _)
  have hh := Real.rpow_le_rpow_of_exponent_le hv (by norm_num : (5 : ℝ) ≤ 73/5)
  simpa only [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast] using hh

/-- The actual centered inverse-residue prefix satisfies the full published Korolev range estimate. -/
theorem korolev_range_estimate : KorolevInverseFractionRangeEstimate := by
  obtain ⟨K, hK, hsource⟩ := KorolevSourcePrefixBound.eventual_source_prefix_bound 1 (by norm_num)
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ r X : ℕ, r.Coprime m →
      korolevLowerRange m ≤ (X : ℝ) → (X : ℝ) ≤ korolevUpperRange m →
      |inverseResiduePrefix m r X| ≤ (1+K/2)*(X : ℝ)*korolevPrefixDecay m X := by
    filter_upwards [hsource, ht.eventually_ge_atTop 1, hlog.eventually_gt_atTop 1,
      eventually_ge_atTop (2 : ℕ)] with m hb hv hL hm r X hr hlo hhi
    letI : NeZero m := ⟨by omega⟩
    dsimp only [Function.comp_apply] at hv
    have hweak := (source_lower_le_published hv).trans hlo
    have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    obtain ⟨hx, hY, hulo, hule⟩ := source_log_range hmR hL hweak hhi
    have hu0 : 0 < Real.log (Real.log X) := by
      have hlogv := Real.log_nonneg hv
      linarith
    have hfull := hb X r hweak hhi hr
    have hgamma := gamma_error_le (c := 0) hv hule
    have hidentity := source_decay_identity (C := 1) (m := (m : ℝ))
      (x := (X : ℝ)) hY hu0.ne'
    simp only [Real.log_one] at hidentity
    rw [hidentity] at hgamma
    simp only [zero_div, Real.exp_zero, one_mul] at hgamma
    have hdec := decay_coordinates (m := m) (X := X) (by linarith) hY (by linarith)
    rw [← hdec] at hgamma
    have hinv := inverse_exp_le_decay hv hule
    rw [Real.exp_log (by linarith : 0 < Real.log (m : ℝ)), ← hdec] at hinv
    have hsmall : (X : ℝ)/Real.log m ≤ (X : ℝ)*korolevPrefixDecay m X := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg X)
    have herror : (K*(X : ℝ)*Real.log (Real.log X)*
        (Real.log X)^(-sourceGamma 1 m X))/2 ≤
        (K/2)*(X : ℝ)*korolevPrefixDecay m X := by
      have hh := mul_le_mul_of_nonneg_left hgamma (show 0 ≤ K*(X : ℝ)/2 by positivity)
      calc
        _ = (K*(X : ℝ)/2)*(Real.log (Real.log X)*
            (Real.log X)^(-sourceGamma 1 m X)) := by ring
        _ ≤ (K*(X : ℝ)/2)*korolevPrefixDecay m X := hh
        _ = _ := by ring
    calc
      _ ≤ (X : ℝ)/Real.log m +
          (K*(X : ℝ)*Real.log (Real.log X)*(Real.log X)^(-sourceGamma 1 m X))/2 := hfull
      _ ≤ (X : ℝ)*korolevPrefixDecay m X+(K/2)*(X : ℝ)*korolevPrefixDecay m X :=
        add_le_add hsmall herror
      _ = _ := by ring
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp hbound
  exact ⟨1+K/2, by linarith, threshold, fun m r X hm hr hlo hhi =>
    hthreshold m hm r X hr hlo hhi⟩

end NField.Alignment.KorolevRangeEstimate
