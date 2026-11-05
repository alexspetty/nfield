/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianBarrierLower
import NField.Alignment.HarperGaussianMaximumInterval

/-!
# Additive and relative changes of a finite Gaussian barrier

A barrier between b and b+w differs from the constant barrier only on a
maximum-window event. The proved survival lower bound converts this
absolute interval error into a relative bound, retaining the actual law.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianBarrierPerturbation
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPathTransfer HarperKilledPath
  HarperPathMaximum HarperGaussianMaximumInterval HarperGaussianBarrierLower

def barrierEvent {n : ℕ} (h : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | ∀ j, partialSum z j ≤ h j}

theorem measurableSet_barrierEvent {n : ℕ} (h : Fin n → ℝ) :
    MeasurableSet (barrierEvent h) := by
  unfold barrierEvent
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le (partialSum_measurable j) measurable_const)

theorem barrierEvent_mono {n : ℕ} {h g : Fin n → ℝ} (hh : ∀ j, h j ≤ g j) :
    barrierEvent h ⊆ barrierEvent g := fun _ hz j => (hz j).trans (hh j)

theorem barrierEvent_window_cover {n : ℕ} (h : Fin n → ℝ) (b w : ℝ)
    (hh : ∀ j, h j ≤ b+w) :
    barrierEvent h ⊆ survivalEvent b ∪ maximumWindow b w := by
  classical
  intro z hz
  by_cases hb : z ∈ survivalEvent b
  · exact Or.inl hb
  · have hn : ¬ ∀ j, partialSum z j ≤ b := hb
    obtain ⟨j,hj⟩ := not_forall.mp hn
    exact Or.inr ⟨fun j => (hz j).trans (hh j),⟨j,(lt_of_not_ge hj).le⟩⟩

theorem gaussian_barrier_additive {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (h : Fin n → ℝ) (b : ℝ) {w : ℝ} (hw : 1 ≤ w) (hh : ∀ j, h j ≤ b+w) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (barrierEvent h) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent b)+
        3000*w/Real.sqrt (n : ℝ) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  calc
    _ ≤ μ.real (survivalEvent b ∪ maximumWindow b w) :=
      measureReal_mono (barrierEvent_window_cover h b w hh) (by finiteness)
    _ ≤ μ.real (survivalEvent b)+μ.real (maximumWindow b w) := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (gaussian_maximum_interval hn v hv b hw)

theorem gaussian_constant_barrier_scaled_lower {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    {b d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) (hds : d ≤ Real.sqrt (n : ℝ)) :
    barrierLowerConstant*d/Real.sqrt (n : ℝ) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent b) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hr : d/Real.sqrt (n : ℝ) ≤ min 1 (b/Real.sqrt (n : ℝ)) :=
    le_min ((div_le_one hs).mpr hds) (div_le_div_of_nonneg_right hdb hs.le)
  calc
    _ = barrierLowerConstant*(d/Real.sqrt (n : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr barrierLowerConstant_pos.le
    _ ≤ _ := gaussian_constant_barrier_lower hn v hv (hd.trans hdb)

theorem gaussian_barrier_relative {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (h : Fin n → ℝ) {b d w : ℝ} (hd : 0 < d) (hdb : d ≤ b)
    (hds : d ≤ Real.sqrt (n : ℝ)) (hw : 1 ≤ w)
    (hl : ∀ j, b ≤ h j) (hu : ∀ j, h j ≤ b+w) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent b) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (barrierEvent h) ∧
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (barrierEvent h) ≤
      (1+3000*w/(barrierLowerConstant*d))*
        (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent b) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  refine ⟨measureReal_mono (fun z hz j => (hz j).trans (hl j)) (by finiteness),?_⟩
  have hs := gaussian_constant_barrier_scaled_lower hn v hv hd.le hdb hds
  have he : 3000*w/Real.sqrt (n : ℝ) ≤
      (3000*w/(barrierLowerConstant*d))*μ.real (survivalEvent b) := by
    calc
      _ = (3000*w/(barrierLowerConstant*d))*(barrierLowerConstant*d/Real.sqrt (n : ℝ)) := by
        field_simp [barrierLowerConstant_pos.ne',hd.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hs
        (div_nonneg (by positivity) (mul_nonneg barrierLowerConstant_pos.le hd.le))
  calc
    _ ≤ μ.real (survivalEvent b)+3000*w/Real.sqrt (n : ℝ) := gaussian_barrier_additive hn v hv h b hw hu
    _ ≤ μ.real (survivalEvent b)+(3000*w/(barrierLowerConstant*d))*μ.real (survivalEvent b) :=
      add_le_add le_rfl he
    _ = _ := by ring

end NField.Alignment.HarperGaussianBarrierPerturbation
