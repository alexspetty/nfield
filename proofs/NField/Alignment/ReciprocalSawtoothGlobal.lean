/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalSmoothedBlock
import NField.Alignment.ReciprocalSmoothingCutoff
import NField.Alignment.ReciprocalDyadicPartition
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The global reciprocal sawtooth bound with all truncated blocks retained -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSawtoothGlobal
open scoped BigOperators Classical
open ReciprocalFloorSmoothing ReciprocalSmoothedBlock ReciprocalSmoothingCutoff
  ReciprocalDyadicPartition

theorem floor_block_bound (p M : ℕ) (X T : ℝ)
    (hp : 1≤p) (hM : M≤p) (hpX : (p : ℝ)≤X) (hT : 1≤T)
    (hXT : X^2≤T^3) (hlog : X*(2+Real.log (X^2))^3≤T^2) :
    |floorSawPrefix p M (X^2)|≤1400*T := by
  by_cases hs : (p : ℝ)≤2*T
  · have hM' : (M : ℝ)≤p := by exact_mod_cast hM
    have hh := floor_saw_prefix_trivial p M (X^2)
    linarith
  · obtain ⟨hH,hHp,hHT,hfreq,hbase,hmass⟩ :=
      cutoff_constraints p X T hT (lt_of_not_ge hs) hpX hXT hlog
    exact floor_block_bound_with_cutoff p M ⌈(p : ℝ)/T⌉₊ X T hp hM hH hpX hHT
      (by linarith) hXT hbase hfreq hmass

set_option maxHeartbeats 400000 in
theorem floor_global_block_sum (Y : ℕ) (X T : ℝ)
    (hYX : (Y : ℝ)≤X) (hT : 1≤T)
    (hXT : X^2≤T^3) (hlog : X*(2+Real.log (X^2))^3≤T^2) :
    |floorSawPrefix 0 Y (X^2)|≤2+1400*T*(Nat.log 2 Y : ℝ) := by
  have hpart := full_prefix_partition (fun n => floorSaw (X^2/(n : ℝ)))
    Y (Nat.log 2 Y) (logarithmic_cover Y)
  have hinit : |prefixSum (fun n => floorSaw (X^2/(n : ℝ))) (min Y 4)|≤2 := by
    have hb := floor_saw_prefix_trivial 0 (min Y 4) (X^2)
    have hm : ((min Y 4 : ℕ) : ℝ)≤4 := by exact_mod_cast min_le_right Y 4
    have hh : |floorSawPrefix 0 (min Y 4) (X^2)|≤2 := by linarith
    simpa only [floorSawPrefix,prefixSum,zero_add] using hh
  have hblock (j : ℕ) :
      |∑ i ∈ Finset.range (length Y j), floorSaw (X^2/((start j+i+1 : ℕ) : ℝ))|≤1400*T := by
    by_cases hj : start j≤Y
    · have hs : 1 ≤ start j := by
        have hh : 0<2^j := by positivity
        unfold start
        omega
      exact floor_block_bound (start j) (length Y j) X T hs (length_le_start Y j)
        ((by exact_mod_cast hj : (start j : ℝ)≤Y).trans hYX) hT hXT hlog
    · have he : length Y j=0 := by
        simp only [length,Nat.sub_eq_zero_of_le (by omega : Y ≤ start j),min_zero]
      simp only [he,Finset.range_zero,Finset.sum_empty,abs_zero]
      linarith
  have he : floorSawPrefix 0 Y (X^2)=prefixSum (fun n => floorSaw (X^2/(n : ℝ))) Y := by
    simp only [floorSawPrefix,prefixSum,zero_add]
  rw [he,hpart]
  calc
    _ ≤ |prefixSum (fun n => floorSaw (X^2/(n : ℝ))) (min Y 4)|+
        |∑ j ∈ Finset.range (Nat.log 2 Y),
          ∑ i ∈ Finset.range (length Y j),floorSaw (X^2/((start j+i+1 : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ 2+∑ j ∈ Finset.range (Nat.log 2 Y),
          |∑ i ∈ Finset.range (length Y j),floorSaw (X^2/((start j+i+1 : ℕ) : ℝ))| :=
      add_le_add hinit (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 2+∑ _j ∈ Finset.range (Nat.log 2 Y),1400*T :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hblock j))
    _ = _ := by simp; ring

/-- Title: `The global floor sawtooth bound`. -/
theorem floor_global_log_bound (Y : ℕ) (X T : ℝ)
    (hY : 1≤Y) (hYX : (Y : ℝ)≤X) (hT : 1≤T)
    (hXT : X^2≤T^3) (hlog : X*(2+Real.log (X^2))^3≤T^2) :
    |floorSawPrefix 0 Y (X^2)|≤2+1400*T*(Real.log X/Real.log 2) := by
  have hY0 : (0 : ℝ)<Y := by exact_mod_cast (by omega : 0<Y)
  have hT0 : 0≤T := by linarith
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hN : (Nat.log 2 Y : ℝ)≤Real.log X/Real.log 2 := by
    have hh := Real.natLog_le_logb Y 2
    simp only [Real.logb,Nat.cast_ofNat] at hh
    exact hh.trans (div_le_div_of_nonneg_right (Real.log_le_log hY0 hYX) hl2.le)
  have hm := mul_le_mul_of_nonneg_left hN (show 0≤1400*T by positivity)
  exact (floor_global_block_sum Y X T hYX hT hXT hlog).trans (add_le_add le_rfl hm)

end NField.Alignment.ReciprocalSawtoothGlobal
