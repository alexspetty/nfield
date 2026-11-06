/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalSawtoothSmoothing

/-! # Exact smoothing of the floor sawtooth, including integer atoms -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalFloorSmoothing
open scoped BigOperators Classical
open CollisionDedekindPairing RealSawtoothDistribution BernoulliSymmetricSmoothing
  ReciprocalArcBlock ReciprocalSecondMoment ReciprocalWeightedBlocks ReciprocalSawtoothSmoothing

def floorSaw (y : ℝ) : ℝ := Int.fract y-1/2

theorem floorSaw_abs_bound (y : ℝ) : |floorSaw y| ≤ 1/2 := by
  unfold floorSaw
  rw [abs_le]
  constructor <;> linarith [Int.fract_nonneg y,Int.fract_lt_one y]

theorem floor_smoothing_error_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (y : ℝ) :
    |floorSaw y-smoothedSaw δ y| ≤ if ∃ z : ℤ, |y-z| ≤ δ then 1 else 0 := by
  split_ifs with h
  · have hab := abs_add_le (floorSaw y) (-smoothedSaw δ y)
    simp only [abs_neg,← sub_eq_add_neg] at hab
    linarith [floorSaw_abs_bound y,smoothed_abs_le_half hδ hδ1 y]
  · have hfract : Int.fract y ≠ 0 := by
      intro hz
      apply h
      refine ⟨⌊y⌋,?_⟩
      change |Int.fract y| ≤ δ
      rw [hz,abs_zero]
      exact hδ.le
    rw [smoothed_eq_saw_of_no_arc hδ h]
    simp [floorSaw,CollisionDedekindPairing.periodicSawtooth,hfract]

def floorSawPrefix (p M : ℕ) (Q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, floorSaw (Q/((p+i+1 : ℕ) : ℝ))

theorem floor_saw_prefix_trivial (p M : ℕ) (Q : ℝ) : |floorSawPrefix p M Q| ≤ M/2 := by
  unfold floorSawPrefix
  calc
    _ ≤ ∑ i ∈ Finset.range M, |floorSaw (Q/((p+i+1 : ℕ) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range M, (1/2 : ℝ) :=
      Finset.sum_le_sum (fun _ _ => floorSaw_abs_bound _)
    _ = _ := by simp; ring

/-- The exact smoothing error is paid only at the selected short-arc points. -/
theorem floor_block_smoothing_error (p M H : ℕ) (X T : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hH : 2 ≤ H) (hpX : (p : ℝ) ≤ X)
    (hHT : (p : ℝ)/(H : ℝ) ≤ T) (hT : 0 < T)
    (hX : X^2 ≤ T^3) (hlog : (p : ℝ)*(1+Real.log p) ≤ 4*T^2) :
    |floorSawPrefix p M (X^2)-smoothedPrefix p M (X^2) (1/(H : ℝ))| ≤ 1160*T := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hδ : 0 < 1/(H : ℝ) := by positivity
  have hδ1 : 1/(H : ℝ) ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2)
    exact_mod_cast hH
  let s := (Finset.range M).filter fun i =>
    ∃ z : ℤ, |X^2/((p+i+1 : ℕ) : ℝ)-z| ≤ 1/(H : ℝ)
  have herr : |floorSawPrefix p M (X^2)-smoothedPrefix p M (X^2) (1/(H : ℝ))| ≤
      (s.card : ℝ) := by
    unfold floorSawPrefix smoothedPrefix
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range M,
          |floorSaw (X^2/((p+i+1 : ℕ) : ℝ))-
            smoothedSaw (1/(H : ℝ)) (X^2/((p+i+1 : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range M,
          if ∃ z : ℤ, |X^2/((p+i+1 : ℕ) : ℝ)-z| ≤ 1/(H : ℝ) then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun _ _ => floor_smoothing_error_bound hδ hδ1 _)
      _ = _ := by simp [s,Finset.sum_boole]
  apply herr.trans
  apply reciprocal_arc_block p M X ((p : ℝ)/(H : ℝ)) T s hp hM hpX
    (by positivity) hHT hT hX hlog (Finset.filter_subset _ _)
  intro i hi
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨z,?_⟩
  have he : ((p : ℝ)/(H : ℝ))/(p : ℝ)=1/(H : ℝ) := by field_simp
  rwa [he]

end NField.Alignment.ReciprocalFloorSmoothing
