/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothingExpectation

/-!
# From smoothed expectations to closed-interval probabilities

If the comparison probability law gives every interval mass at most M
times its length, boundary strips cost at most their total length times M.
The two actual kernel sandwiches and compact Fourier comparison then
give an explicit two-sided interval error. All assumptions on the
comparison law and characteristic functions remain visible here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperIntervalProbability
open scoped Topology
open MeasureTheory Set HarperIntervalSmoothing HarperSmoothingExpectation

theorem interval_expansion_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {M r : ℝ} (hr : 0 ≤ r)
    (hν : ∀ a b : ℝ, ν.real (Icc a b) ≤ M*max (b-a) 0) (a b : ℝ) :
    ν.real (Icc (a-r) (b+r)) ≤ ν.real (Icc a b)+2*M*r := by
  have hsub : Icc (a-r) (b+r) ⊆ Icc a b ∪ (Icc (a-r) a ∪ Icc b (b+r)) := by
    intro z hz
    by_cases hza : z < a
    · exact Or.inr (Or.inl ⟨hz.1,hza.le⟩)
    · by_cases hzb : z ≤ b
      · exact Or.inl ⟨le_of_not_gt hza,hzb⟩
      · exact Or.inr (Or.inr ⟨(lt_of_not_ge hzb).le,hz.2⟩)
  have h1 := hν (a-r) a
  have h2 := hν b (b+r)
  have hlen1 : a-(a-r) = r := by ring
  have hlen2 : b+r-b = r := by ring
  rw [hlen1,max_eq_left hr] at h1
  rw [hlen2,max_eq_left hr] at h2
  calc
    _ ≤ ν.real (Icc a b ∪ (Icc (a-r) a ∪ Icc b (b+r))) := measureReal_mono hsub
    _ ≤ ν.real (Icc a b)+(ν.real (Icc (a-r) a)+ν.real (Icc b (b+r))) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ _ := by linarith

theorem interval_contraction_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {M r : ℝ} (hr : 0 ≤ r)
    (hν : ∀ a b : ℝ, ν.real (Icc a b) ≤ M*max (b-a) 0) (a b : ℝ) :
    ν.real (Icc a b) ≤ ν.real (Icc (a+r) (b-r))+2*M*r := by
  have hsub : Icc a b ⊆ Icc (a+r) (b-r) ∪ (Icc a (a+r) ∪ Icc (b-r) b) := by
    intro z hz
    by_cases hza : z < a+r
    · exact Or.inr (Or.inl ⟨hz.1,hza.le⟩)
    · by_cases hzb : z ≤ b-r
      · exact Or.inl ⟨le_of_not_gt hza,hzb⟩
      · exact Or.inr (Or.inr ⟨(lt_of_not_ge hzb).le,hz.2⟩)
  have h1 := hν a (a+r)
  have h2 := hν (b-r) b
  have hlen1 : a+r-a = r := by ring
  have hlen2 : b-(b-r) = r := by ring
  rw [hlen1,max_eq_left hr] at h1
  rw [hlen2,max_eq_left hr] at h2
  calc
    _ ≤ ν.real (Icc (a+r) (b-r) ∪ (Icc a (a+r) ∪ Icc (b-r) b)) := measureReal_mono hsub
    _ ≤ ν.real (Icc (a+r) (b-r))+(ν.real (Icc a (a+r))+ν.real (Icc (b-r) b)) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ _ := by linarith

theorem interval_probability_comparison (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {delta h M E : ℝ} (hd : 0 < delta) (hh : 0 < h) (hE : 0 ≤ E)
    (hν : ∀ a b : ℝ, ν.real (Icc a b) ≤ M*max (b-a) 0)
    (hcf : ∀ u : ℝ, |u| ≤ 2*Real.pi*delta⁻¹ → ‖charFun μ u-charFun ν u‖ ≤ E)
    (a b : ℝ) :
    |μ.real (Icc a b)-ν.real (Icc a b)| ≤
      2*max (b-a+2*h) 0*delta⁻¹*E+4*M*h+2*tailAllowance delta h := by
  have he := abs_le.mp (intervalWindow_expectation_error μ ν hd hE (a-h) (b+h) hcf)
  have hc := abs_le.mp (intervalWindow_expectation_error μ ν hd hE (a+h) (b-h) hcf)
  have hlen : b+h-(a-h) = b-a+2*h := by ring
  rw [hlen] at he
  have hcontract : 2*max (b-h-(a+h)) 0*delta⁻¹*E ≤
      2*max (b-a+2*h) 0*delta⁻¹*E := by
    apply mul_le_mul_of_nonneg_right _ hE
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd.le)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max_right 0 (by linarith)
  have hμup := intervalProbability_le_expanded_expectation μ hd hh a b
  have hμlo := contracted_expectation_le_intervalProbability μ hd hh a b
  have hνup := contracted_expectation_le_intervalProbability ν hd hh (a-2*h) (b+2*h)
  have hνlo := intervalProbability_le_expanded_expectation ν hd hh (a+2*h) (b-2*h)
  have h1 : a-2*h+h = a-h := by ring
  have h2 : b+2*h-h = b+h := by ring
  have h3 : a+2*h-h = a+h := by ring
  have h4 : b-2*h+h = b-h := by ring
  rw [h1,h2] at hνup
  rw [h3,h4] at hνlo
  have hex := interval_expansion_bound ν (show 0 ≤ 2*h by positivity) hν a b
  have hcon := interval_contraction_bound ν (show 0 ≤ 2*h by positivity) hν a b
  apply abs_le.mpr
  constructor <;> linarith

end NField.Alignment.HarperIntervalProbability
