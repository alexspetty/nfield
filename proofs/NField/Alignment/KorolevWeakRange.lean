/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.KorolevRangeEstimate

/-! # The spare source range needed for literal real cutoffs -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevWeakRange
open Filter KorolevSourceWindowCount KorolevSourceScales KorolevRangeEstimate
  DedekindInverseResidueTransform
open scoped Topology

/-- The actual prefix estimate also holds at the weaker source threshold. -/
theorem weak_range_estimate : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ m : ℕ in atTop,
    ∀ r X : ℕ, r.Coprime m →
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ (X : ℝ) →
      (X : ℝ) ≤ korolevUpperRange m →
      |inverseResiduePrefix m r X| ≤ K*(X : ℝ)*korolevPrefixDecay m X := by
  obtain ⟨K, hK, hsource⟩ := KorolevSourcePrefixBound.eventual_source_prefix_bound 1 (by norm_num)
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ r X : ℕ, r.Coprime m →
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ (X : ℝ) → (X : ℝ) ≤ korolevUpperRange m →
      |inverseResiduePrefix m r X| ≤ (1+K/2)*(X : ℝ)*korolevPrefixDecay m X := by
    filter_upwards [hsource, ht.eventually_ge_atTop 1, hlog.eventually_gt_atTop 1,
      eventually_ge_atTop (2 : ℕ)] with m hb hv hL hm r X hr hlo hhi
    letI : NeZero m := ⟨by omega⟩
    dsimp only [Function.comp_apply] at hv
    have hweak := hlo
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
  exact ⟨1+K/2, by linarith, hbound⟩

end NField.Alignment.KorolevWeakRange
