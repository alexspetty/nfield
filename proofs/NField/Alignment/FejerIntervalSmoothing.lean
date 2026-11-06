/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerKernel

/-! # Pointwise smoothing of interval indicators

Integrate the positive periodic kernel over an enlarged real interval.
The interval is allowed to cross a period boundary or exceed one period;
this retains endpoint atoms without a case split for wrapped arcs.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.FejerIntervalSmoothing

open MeasureTheory Set
open FejerKernel

/-- An unwrapped interval convolved with the periodic kernel. -/
def window (H : ℕ) (a b : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  ∫ t in a..b, kernel H (x - (t : AddCircle (1 : ℝ)))

/-- Normalize an enlarged interval by the retained central kernel mass. -/
def majorant (H : ℕ) (δ a b : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  window H (a - δ) (b + δ) x / (1 - 1 / (2 * (H : ℝ) * δ))

theorem continuous_window_integrand (H : ℕ) (x : AddCircle (1 : ℝ)) :
    Continuous (fun t : ℝ => kernel H (x - (t : AddCircle (1 : ℝ)))) :=
  (continuous_kernel H).comp (continuous_const.sub (AddCircle.continuous_mk' 1))

theorem window_nonneg (H : ℕ) (a b : ℝ) (hab : a ≤ b) (x : AddCircle (1 : ℝ)) :
    0 ≤ window H a b x := by
  exact intervalIntegral.integral_nonneg_of_forall hab (fun t => kernel_nonneg H _)

/-- A window centered at the evaluation point has the central kernel mass. -/
theorem window_central (H : ℕ) (δ t : ℝ) :
    window H (t - δ) (t + δ) (t : AddCircle (1 : ℝ)) =
      ∫ u in (-δ)..δ, kernel H (u : AddCircle (1 : ℝ)) := by
  unfold window
  simp_rw [← AddCircle.coe_sub]
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => kernel H (u : AddCircle (1 : ℝ))) t]
  congr 1 <;> ring

/-- Every point of the original closed interval retains the full central mass. -/
theorem window_lower_bound (H : ℕ) (hH : 0 < H) (δ a b t : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ht : t ∈ Icc a b) :
    1 - 1 / (2 * (H : ℝ) * δ) ≤
      window H (a - δ) (b + δ) (t : AddCircle (1 : ℝ)) := by
  calc
    _ ≤ ∫ u in (-δ)..δ, kernel H (u : AddCircle (1 : ℝ)) :=
      central_mass_lower_bound H hH δ hδ hδ'
    _ = window H (t - δ) (t + δ) (t : AddCircle (1 : ℝ)) := (window_central H δ t).symm
    _ ≤ _ := intervalIntegral.integral_mono_interval
      (by linarith [ht.1]) (by linarith) (by linarith [ht.2])
      (Filter.Eventually.of_forall (fun u => kernel_nonneg H _))
      ((continuous_window_integrand H (t : AddCircle (1 : ℝ))).intervalIntegrable _ _)

theorem normalization_pos (H : ℕ) (δ : ℝ) (hscale : 1 < 2 * (H : ℝ) * δ) :
    0 < 1 - 1 / (2 * (H : ℝ) * δ) := by
  have hp : 0 < 2 * (H : ℝ) * δ := by linarith
  have ht := (div_lt_one hp).mpr hscale
  linarith

theorem majorant_nonneg (H : ℕ) (δ a b : ℝ) (x : AddCircle (1 : ℝ))
    (hδ : 0 < δ) (hab : a ≤ b) (hscale : 1 < 2 * (H : ℝ) * δ) :
    0 ≤ majorant H δ a b x := by
  exact div_nonneg (window_nonneg H _ _ (by linarith) x) (normalization_pos H δ hscale).le

theorem one_le_majorant (H : ℕ) (hH : 0 < H) (δ a b t : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hscale : 1 < 2 * (H : ℝ) * δ)
    (ht : t ∈ Icc a b) : 1 ≤ majorant H δ a b (t : AddCircle (1 : ℝ)) := by
  apply (le_div_iff₀ (normalization_pos H δ hscale)).mpr
  simpa only [one_mul] using window_lower_bound H hH δ a b t hδ hδ' ht

/-- The strict threshold indicator is bounded above at every real sample, including integers. -/
theorem threshold_upper (H : ℕ) (hH : 0 < H) (δ α t : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hscale : 1 < 2 * (H : ℝ) * δ)
    (hα0 : 0 ≤ α) :
    (if Int.fract t < α then (1 : ℝ) else 0) ≤
      majorant H δ 0 α (t : AddCircle (1 : ℝ)) := by
  by_cases ht : Int.fract t < α
  · rw [if_pos ht]
    simpa only [AddCircle.coe_fract] using
      one_le_majorant H hH δ 0 α (Int.fract t) hδ hδ' hscale ⟨Int.fract_nonneg t, ht.le⟩
  · rw [if_neg ht]
    exact majorant_nonneg H δ 0 α _ hδ hα0 hscale

/-- The complementary closed interval supplies a lower bound for the strict indicator.
The equality case `fract t = α` is included in the complement. -/
theorem threshold_lower (H : ℕ) (hH : 0 < H) (δ α t : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hscale : 1 < 2 * (H : ℝ) * δ)
    (hα1 : α ≤ 1) :
    1 - majorant H δ α 1 (t : AddCircle (1 : ℝ)) ≤
      (if Int.fract t < α then (1 : ℝ) else 0) := by
  by_cases ht : Int.fract t < α
  · rw [if_pos ht]
    linarith [majorant_nonneg H δ α 1 (t : AddCircle (1 : ℝ)) hδ hα1 hscale]
  · rw [if_neg ht]
    have hb := one_le_majorant H hH δ α 1 (Int.fract t) hδ hδ' hscale
      ⟨le_of_not_gt ht, (Int.fract_lt_one t).le⟩
    rw [AddCircle.coe_fract] at hb
    linarith

end NField.Alignment.FejerIntervalSmoothing
