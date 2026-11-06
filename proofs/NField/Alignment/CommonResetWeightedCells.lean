/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedCurvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Literal affine cells and one-sided readings of the weighted clock profile -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedCells

open scoped BigOperators
open Set MeasureTheory CollisionRampEnergy CommonResetGram CommonResetWeightedSampling

def cellClock (D j k : ℕ) (x : ℝ) : ℝ :=
  (j : ℝ)*x-((k/(D/j) : ℕ) : ℝ)-1/2

def cellProfile (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  2*∑ j ∈ Finset.Icc 1 N, c j*cellClock D j k x

def gridReset (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, if k%(D/j)=0 then c j else 0

theorem quotient_pos {D j : ℕ} (hD : 0 < D) (hj : 0 < j) (hd : j ∣ D) : 0 < D/j :=
  Nat.div_pos (Nat.le_of_dvd hD hd) hj

theorem clock_argument {D j : ℕ} (hj : 0 < j) (hd : j ∣ D) (k : ℕ) (t : ℝ) :
    (j : ℝ)*(((k : ℝ)+t)/D)=((k : ℝ)+t)/((D/j : ℕ) : ℝ) := by
  have he : (D : ℝ)=(j : ℝ)*(D/j : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  rw [he]
  field_simp

theorem cellClock_parameter {D j : ℕ} (hD : 0 < D) (hj : 0 < j) (hd : j ∣ D)
    (k : ℕ) (t : ℝ) :
    cellClock D j k (((k : ℝ)+t)/D)=(((k%(D/j) : ℕ) : ℝ)+t)/((D/j : ℕ) : ℝ)-1/2 := by
  unfold cellClock
  rw [clock_argument hj hd]
  have he : (k : ℝ)=((k%(D/j) : ℕ) : ℝ)+(D/j : ℕ)*(k/(D/j) : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k (D/j)).symm
  have hs : ((D/j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (quotient_pos hD hj hd).ne'
  rw [he]
  field_simp
  ring

/-- Title: `The actual weighted clocks agree with their affine polynomial on every open common-grid cell`. -/
theorem midpointRow_on_common_cell {D j : ℕ} (hD : 0 < D) (hj : 0 < j) (hd : j ∣ D)
    (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    midpointRow j (((k : ℝ)+t)/D)=cellClock D j k (((k : ℝ)+t)/D) := by
  have hs := quotient_pos hD hj hd
  have hz : (((k%(D/j) : ℕ) : ℝ)+t)/((D/j : ℕ) : ℝ) ≠ 0 := (by positivity :
    0 < (((k%(D/j) : ℕ) : ℝ)+t)/((D/j : ℕ) : ℝ)).ne'
  rw [midpointRow, affineRow, clock_argument hj hd, fract_affine_cell hs k ht0.le ht1,
    if_neg hz, cellClock_parameter hD hj hd]

theorem weightedProfile_on_common_cell {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ)
    {x : ℝ} (hx : x ∈ Ioo ((k : ℝ)/D) (((k : ℝ)+1)/D)) :
    weightedProfile N c x=cellProfile N D c k x := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let t := (D : ℝ)*x-k
  have ht0 : 0 < t := by dsimp [t]; nlinarith [(div_lt_iff₀ hDR).mp hx.1]
  have ht1 : t < 1 := by dsimp [t]; nlinarith [(lt_div_iff₀ hDR).mp hx.2]
  have he : x=((k : ℝ)+t)/D := by dsimp [t]; field_simp; ring
  unfold weightedProfile cellProfile
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [he, midpointRow_on_common_cell hD (Finset.mem_Icc.mp hj).1 (hdiv j hj) k ht0 ht1]

theorem clock_right_value {D j : ℕ} (hD : 0 < D) (hj : 0 < j) (hd : j ∣ D) (k : ℕ) :
    cellClock D j k ((k : ℝ)/D)=midpointRow j ((k : ℝ)/D)-
      (if k%(D/j)=0 then (1/2 : ℝ) else 0) := by
  have hs := quotient_pos hD hj hd
  have he := cellClock_parameter hD hj hd k 0
  simp only [add_zero] at he
  rw [he, midpointRow, affineRow]
  have ha := clock_argument hj hd k 0
  simp only [add_zero] at ha
  rw [ha]
  have hf := fract_affine_cell hs k (t := 0) (by norm_num) (by norm_num)
  simp only [add_zero] at hf
  rw [hf]
  by_cases hz : k%(D/j)=0
  · simp [hz]
  · have hzR : (((k%(D/j) : ℕ) : ℝ)/((D/j : ℕ) : ℝ)) ≠ 0 := div_ne_zero
      (by exact_mod_cast hz) (by exact_mod_cast hs.ne')
    simp [hz, hzR]

theorem residue_successor {s : ℕ} (hs : 0 < s) (k : ℕ) :
    if (k+1)%s=0 then k%s+1=s else (k+1)%s=k%s+1 := by
  have hmod : (k+1)%s=(k%s+1)%s := by simp only [Nat.add_mod, Nat.mod_mod]
  have hk := Nat.mod_lt k hs
  by_cases he : k%s+1=s
  · simp [hmod, he]
  · have hl : k%s+1<s := by omega
    rw [hmod, Nat.mod_eq_of_lt hl, if_neg (by omega)]

theorem clock_left_value {D j : ℕ} (hD : 0 < D) (hj : 0 < j) (hd : j ∣ D) (k : ℕ) :
    cellClock D j k (((k : ℝ)+1)/D)=midpointRow j (((k : ℝ)+1)/D)+
      (if (k+1)%(D/j)=0 then (1/2 : ℝ) else 0) := by
  have hs := quotient_pos hD hj hd
  have hsR : ((D/j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [cellClock_parameter hD hj hd k 1, midpointRow, affineRow, clock_argument hj hd]
  have hf := fract_affine_cell hs (k+1) (t := 0) (by norm_num) (by norm_num)
  simp only [add_zero, Nat.cast_add, Nat.cast_one] at hf
  rw [hf]
  have hsucc := residue_successor hs k
  by_cases hz : (k+1)%(D/j)=0
  · rw [if_pos hz] at hsucc
    have hcast : ((k%(D/j) : ℕ) : ℝ)+1=(D/j : ℕ) := by exact_mod_cast hsucc
    norm_num [hz, hcast, hsR]
  · rw [if_neg hz] at hsucc
    have hcast : (((k+1)%(D/j) : ℕ) : ℝ)=((k%(D/j) : ℕ) : ℝ)+1 := by exact_mod_cast hsucc
    have hzR : ((((k+1)%(D/j) : ℕ) : ℝ)/((D/j : ℕ) : ℝ)) ≠ 0 := div_ne_zero
      (by exact_mod_cast hz) hsR
    rw [if_neg hzR, if_neg hz, hcast]
    ring

theorem cell_right_value {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ) :
    cellProfile N D c k ((k : ℝ)/D)=weightedProfile N c ((k : ℝ)/D)-gridReset N D c k := by
  unfold cellProfile weightedProfile gridReset
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [clock_right_value hD (Finset.mem_Icc.mp hj).1 (hdiv j hj)]
  split_ifs <;> ring

theorem cell_left_value {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ) :
    cellProfile N D c k (((k : ℝ)+1)/D)=weightedProfile N c (((k : ℝ)+1)/D)+gridReset N D c (k+1) := by
  unfold cellProfile weightedProfile gridReset
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [clock_left_value hD (Finset.mem_Icc.mp hj).1 (hdiv j hj)]
  split_ifs <;> ring

theorem cellProfile_derivative (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (cellProfile N D c k) (2*slopeMoment N c) x := by
  unfold cellProfile slopeMoment cellClock
  have h := (HasDerivAt.fun_sum (u := Finset.Icc 1 N) (fun j _ =>
    ((((hasDerivAt_id x).const_mul (j : ℝ)).sub_const
      (((k/(D/j) : ℕ) : ℝ))).sub_const (1/2)).const_mul (c j))).const_mul 2
  simpa only [id_eq, mul_one, mul_comm] using h

end NField.Alignment.CommonResetWeightedCells
