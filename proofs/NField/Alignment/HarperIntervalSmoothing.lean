/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartitionFourier

/-!
# Positive-kernel bounds for literal closed intervals

The smoothing window is a set integral, so an empty contracted interval
has value zero. The actual normalized sinc-square kernel gives both
pointwise indicator bounds, retaining closed endpoints even for laws
with atoms. These bounds precede the Fourier probability comparison.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperIntervalSmoothing
open scoped Topology
open MeasureTheory Set Filter HarperSincKernel

def intervalWindow (delta a b z : ℝ) : ℝ :=
  ∫ y in Icc (a-z) (b-z), kernel delta y
def tailAllowance (delta h : ℝ) : ℝ := 2*delta/(Real.pi^2*h)

theorem intervalWindow_empty (delta : ℝ) {a b : ℝ} (hab : b < a) (z : ℝ) :
    intervalWindow delta a b z = 0 := by
  simp [intervalWindow, Icc_eq_empty_of_lt (show b-z < a-z by linarith)]

theorem intervalWindow_singleton (delta a z : ℝ) : intervalWindow delta a a z = 0 := by
  simp [intervalWindow]

theorem intervalWindow_nonneg {delta : ℝ} (hd : 0 < delta) (a b z : ℝ) :
    0 ≤ intervalWindow delta a b z := integral_nonneg (kernel_nonneg hd)

theorem intervalWindow_le_one {delta : ℝ} (hd : 0 < delta) (a b z : ℝ) :
    intervalWindow delta a b z ≤ 1 := by
  rw [intervalWindow, ← integral_kernel hd]
  exact setIntegral_le_integral (integrable_kernel hd) (Eventually.of_forall (kernel_nonneg hd))

theorem intervalWindow_measurable (delta a b : ℝ) : Measurable (intervalWindow delta a b) := by
  classical
  let S : Set (ℝ × ℝ) := {p | a ≤ p.1+p.2 ∧ p.1+p.2 ≤ b}
  have hS : MeasurableSet S := (measurableSet_le measurable_const
    (measurable_fst.add measurable_snd)).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
  have hf : Measurable (S.indicator (fun p => kernel delta p.2)) :=
    ((continuous_kernel delta).measurable.comp measurable_snd).indicator hS
  have hm : Measurable (fun z => ∫ y, S.indicator (fun p => kernel delta p.2) (z,y)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  convert hm using 1
  funext z
  rw [intervalWindow, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    have he : y ∈ Icc (a-z) (b-z) ↔ (z,y) ∈ S := by
      change (a-z ≤ y ∧ y ≤ b-z) ↔ (a ≤ z+y ∧ z+y ≤ b)
      constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
    simp only [indicator_apply, he])

theorem intervalWindow_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Integrable (fun ω => intervalWindow delta a b (X ω)) μ := by
  apply Integrable.of_bound ((intervalWindow_measurable delta a b).comp hX).aestronglyMeasurable 1
  exact Eventually.of_forall (fun ω => by
    change ‖intervalWindow delta a b (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalWindow_nonneg hd a b (X ω))]
    exact intervalWindow_le_one hd a b (X ω))

theorem tailAllowance_nonneg {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h) :
    0 ≤ tailAllowance delta h := by unfold tailAllowance; positivity

theorem central_kernel_mass {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h) :
    1-tailAllowance delta h ≤ ∫ y in Icc (-h) h, kernel delta y := by
  have he : (Icc (-h) h)ᶜ = {y : ℝ | h < |y|} := by
    ext y
    simp only [mem_compl_iff, mem_Icc, ← abs_le, mem_setOf_eq, not_le]
  have hs := integral_add_compl (μ := volume) (f := kernel delta)
    (s := Icc (-h) h) measurableSet_Icc
    (integrable_kernel hd)
  rw [he, integral_kernel hd] at hs
  have ht := integral_kernel_tail_le hd hh
  change _ ≤ tailAllowance delta h at ht
  linarith

theorem expandedWindow_lower {delta h a b z : ℝ} (hd : 0 < delta) (hh : 0 < h)
    (hz : z ∈ Icc a b) :
    1-tailAllowance delta h ≤ intervalWindow delta (a-h) (b+h) z := by
  apply (central_kernel_mass hd hh).trans
  apply setIntegral_mono_set (integrable_kernel hd).integrableOn
    (Eventually.of_forall (kernel_nonneg hd))
  exact Eventually.of_forall (fun y hy => by
    rcases hy with ⟨hl,hu⟩
    constructor <;> linarith [hz.1,hz.2])

theorem contractedWindow_upper {delta h a b z : ℝ} (hd : 0 < delta) (hh : 0 < h)
    (hz : z ∉ Icc a b) :
    intervalWindow delta (a+h) (b-h) z ≤ tailAllowance delta h := by
  apply le_trans _ (integral_kernel_tail_le hd hh)
  apply setIntegral_mono_set (integrable_kernel hd).integrableOn
    (Eventually.of_forall (kernel_nonneg hd))
  exact Eventually.of_forall (fun y hy => by
    change h < |y|
    rcases lt_or_ge z a with hz' | hz'
    · exact (show h < y by linarith [hy.1]).trans_le (le_abs_self y)
    · have hb : b < z := lt_of_not_ge (fun he => hz ⟨hz',he⟩)
      exact (show h < -y by linarith [hy.2]).trans_le (neg_le_abs y))

theorem indicator_le_expandedWindow {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h)
    (a b z : ℝ) :
    (Icc a b).indicator (fun _ => (1 : ℝ)) z ≤
      intervalWindow delta (a-h) (b+h) z+tailAllowance delta h := by
  classical
  by_cases hz : z ∈ Icc a b
  · rw [indicator_of_mem hz]
    linarith [expandedWindow_lower hd hh hz]
  · rw [indicator_of_notMem hz]
    exact add_nonneg (intervalWindow_nonneg hd _ _ _) (tailAllowance_nonneg hd hh)

theorem contractedWindow_le_indicator {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h)
    (a b z : ℝ) :
    intervalWindow delta (a+h) (b-h) z ≤
      (Icc a b).indicator (fun _ => (1 : ℝ)) z+tailAllowance delta h := by
  classical
  by_cases hz : z ∈ Icc a b
  · rw [indicator_of_mem hz]
    exact (intervalWindow_le_one hd _ _ _).trans (le_add_of_nonneg_right (tailAllowance_nonneg hd hh))
  · rw [indicator_of_notMem hz, zero_add]
    exact contractedWindow_upper hd hh hz

end NField.Alignment.HarperIntervalSmoothing
