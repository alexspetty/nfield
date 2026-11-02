/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSincKernel

/-!
# Actual localized partition weights

Integrating the normalized positive kernel over adjacent unit windows gives
the finite partition and its outside cell. This file first establishes
positivity, total mass and localization. The all-order derivative estimates
and Taylor approximation are separate obligations.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set

namespace NField.Alignment.HarperPartition

open HarperSincKernel

def cell (delta x : ℝ) : ℝ :=
  ∫ u in (x-1/2)..(x+1/2), HarperSincKernel.kernel delta u

def cellSum (delta : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2*J+1), cell delta (x+(i : ℝ)-J)

def outside (delta : ℝ) (J : ℕ) (x : ℝ) : ℝ := 1-cellSum delta J x

theorem cell_nonneg {delta : ℝ} (hd : 0 < delta) (x : ℝ) : 0 ≤ cell delta x := by
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (kernel_nonneg hd)

theorem cell_as_setIntegral (delta x : ℝ) :
    cell delta x = ∫ u in Icc (x-1/2) (x+1/2), kernel delta u := by
  rw [cell, intervalIntegral.integral_of_le (by linarith : x-1/2 ≤ x+1/2),
    integral_Icc_eq_integral_Ioc]

theorem cell_le_one {delta : ℝ} (hd : 0 < delta) (x : ℝ) : cell delta x ≤ 1 := by
  rw [cell_as_setIntegral, ← integral_kernel hd]
  exact setIntegral_le_integral (integrable_kernel hd) (Filter.Eventually.of_forall (kernel_nonneg hd))

theorem cell_localization {delta x : ℝ} (hd : 0 < delta) (hx : 1 < |x|) :
    cell delta x ≤ delta := by
  rw [cell_as_setIntegral]
  refine (setIntegral_mono_set (integrable_kernel hd).integrableOn
    (Filter.Eventually.of_forall (kernel_nonneg hd)) ?_).trans (integral_kernel_half_tail_le hd)
  filter_upwards with u
  intro hu
  change (1/2 : ℝ) < |u|
  rcases hu with ⟨hlo,hhi⟩
  rcases lt_abs.mp hx with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))

theorem cellSum_as_intervalIntegral (delta : ℝ) (J : ℕ) (x : ℝ) :
    cellSum delta J x = ∫ u in (x-J-1/2)..(x+J+1/2), kernel delta u := by
  let a : ℕ → ℝ := fun i => x-J-1/2+i
  have hs := intervalIntegral.sum_integral_adjacent_intervals (f := kernel delta)
    (μ := volume) (a := a) (n := 2*J+1) (fun i _ => (continuous_kernel delta).intervalIntegrable _ _)
  have he : ∀ i : ℕ, cell delta (x+(i : ℝ)-J) = ∫ u in a i..a (i+1), kernel delta u := by
    intro i
    unfold cell a
    congr 1 <;> push_cast <;> ring
  unfold cellSum
  simp_rw [he]
  rw [hs]
  dsimp only [a]
  congr 1 <;> push_cast <;> ring

theorem cellSum_as_setIntegral (delta : ℝ) (J : ℕ) (x : ℝ) :
    cellSum delta J x = ∫ u in Icc (x-J-1/2) (x+J+1/2), kernel delta u := by
  rw [cellSum_as_intervalIntegral, intervalIntegral.integral_of_le (by have := Nat.cast_nonneg (α := ℝ) J; linarith :
    x-(J : ℝ)-1/2 ≤ x+J+1/2), integral_Icc_eq_integral_Ioc]

theorem cellSum_le_one {delta : ℝ} (hd : 0 < delta) (J : ℕ) (x : ℝ) :
    cellSum delta J x ≤ 1 := by
  rw [cellSum_as_setIntegral, ← integral_kernel hd]
  exact setIntegral_le_integral (integrable_kernel hd) (Filter.Eventually.of_forall (kernel_nonneg hd))

theorem outside_nonneg {delta : ℝ} (hd : 0 < delta) (J : ℕ) (x : ℝ) :
    0 ≤ outside delta J x := sub_nonneg.mpr (cellSum_le_one hd J x)

theorem partition_sum (delta : ℝ) (J : ℕ) (x : ℝ) :
    cellSum delta J x + outside delta J x = 1 := by unfold outside; ring

theorem outside_as_setIntegral {delta : ℝ} (hd : 0 < delta) (J : ℕ) (x : ℝ) :
    outside delta J x = ∫ u in (Icc (x-J-1/2) (x+J+1/2))ᶜ, kernel delta u := by
  have hs := integral_add_compl (s := Icc (x-(J : ℝ)-1/2) (x+J+1/2))
    measurableSet_Icc (integrable_kernel hd)
  rw [integral_kernel hd] at hs
  unfold outside
  rw [cellSum_as_setIntegral]
  linarith

theorem outside_localization {delta : ℝ} (hd : 0 < delta) (J : ℕ) {x : ℝ}
    (hx : |x| ≤ J) : outside delta J x ≤ delta := by
  rw [outside_as_setIntegral hd]
  refine (setIntegral_mono_set (integrable_kernel hd).integrableOn
    (Filter.Eventually.of_forall (kernel_nonneg hd)) ?_).trans (integral_kernel_half_tail_le hd)
  filter_upwards with u
  intro hu
  change (1/2 : ℝ) < |u|
  change ¬ (x-(J : ℝ)-1/2 ≤ u ∧ u ≤ x+J+1/2) at hu
  obtain ⟨hxl,hxu⟩ := abs_le.mp hx
  by_contra h
  obtain ⟨hul,huu⟩ := abs_le.mp (le_of_not_gt h)
  exact hu ⟨by linarith, by linarith⟩

/-- Indices 0 through 2J represent the integer translates J-i; the last
index is the outside cell. There are exactly 2J+2 labels. -/
def labelWeight (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (x : ℝ) : ℝ :=
  if i.val < 2*J+1 then cell delta (x+(i.val : ℝ)-J) else outside delta J x

theorem labelWeight_nonneg {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) (x : ℝ) : 0 ≤ labelWeight delta J i x := by
  unfold labelWeight
  split_ifs
  · exact cell_nonneg hd _
  · exact outside_nonneg hd J x

theorem labelWeight_sum (delta : ℝ) (J : ℕ) (x : ℝ) :
    ∑ i : Fin (2*J+2), labelWeight delta J i x = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [labelWeight, Fin.val_castSucc, Fin.isLt, if_true, Fin.val_last,
    lt_self_iff_false, if_false]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => cell delta (x+(i : ℝ)-J))]
  exact partition_sum delta J x

def boxWeight {A : ℕ} (delta : ℝ) (J : ℕ) (values : Fin A → ℝ)
    (labels : Fin A → Fin (2*J+2)) : ℝ :=
  ∏ i, labelWeight delta J (labels i) (values i)

theorem boxWeight_nonneg {A : ℕ} {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (values : Fin A → ℝ) (labels : Fin A → Fin (2*J+2)) :
    0 ≤ boxWeight delta J values labels :=
  Finset.prod_nonneg (fun i _ => labelWeight_nonneg hd J (labels i) (values i))

theorem boxWeight_sum {A : ℕ} (delta : ℝ) (J : ℕ) (values : Fin A → ℝ) :
    ∑ labels : Fin A → Fin (2*J+2), boxWeight delta J values labels = 1 := by
  unfold boxWeight
  rw [← Fintype.prod_sum (fun (i : Fin A) (j : Fin (2*J+2)) =>
    labelWeight delta J j (values i))]
  simp only [labelWeight_sum, Finset.prod_const_one]

end NField.Alignment.HarperPartition
