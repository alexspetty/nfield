/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeWindows
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Endpoint comparisons and rounded indices

The endpoint definitions imply the rounding bounds directly.

-/


noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevEndpointIndices
open KorolevPrimeWindows

theorem upperEndpoint_le_threshold_iff {L t : ℝ} (ht : 0 < t)
    {k : ℕ} (hk : 1 ≤ k) :
    upperEndpoint L k ≤ Real.exp t/4 ↔ L/(2*t)+1/2 ≤ (k : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 2*(k : ℝ)-1 := by linarith
  unfold upperEndpoint
  rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4), Real.exp_le_exp,
    div_le_iff₀ hd]
  constructor
  · intro h
    have h' : L/(2*t) ≤ (k : ℝ)-1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  · intro h
    have h' : L ≤ ((k : ℝ)-1/2)*(2*t) := (div_le_iff₀ (by positivity)).mp (by linarith : L/(2*t) ≤ (k : ℝ)-1/2)
    nlinarith

theorem threshold_le_upperEndpoint_iff {L t : ℝ} (ht : 0 < t)
    {k : ℕ} (hk : 1 ≤ k) :
    Real.exp t/4 ≤ upperEndpoint L k ↔ (k : ℝ) ≤ L/(2*t)+1/2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 2*(k : ℝ)-1 := by linarith
  unfold upperEndpoint
  rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4), Real.exp_le_exp,
    le_div_iff₀ hd]
  constructor
  · intro h
    have h' : (k : ℝ)-1/2 ≤ L/(2*t) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  · intro h
    have h' : ((k : ℝ)-1/2)*(2*t) ≤ L := (le_div_iff₀ (by positivity)).mp (by linarith : (k : ℝ)-1/2 ≤ L/(2*t))
    nlinarith

theorem endpoint_lower_index_bounds {L t : ℝ} (ht : 0 < t) {k : ℕ}
    (hk : 2 ≤ k) (h : upperEndpoint L k ≤ Real.exp t/4)
    (hprev : Real.exp t/4 < upperEndpoint L (k-1)) :
    L/(2*t)+1/2 ≤ (k : ℝ) ∧ (k : ℝ) < L/(2*t)+3/2 := by
  refine ⟨(upperEndpoint_le_threshold_iff ht (by omega)).mp h, ?_⟩
  have hh := (not_le.mp (mt (upperEndpoint_le_threshold_iff ht (by omega : 1 ≤ k-1)).mpr
    (not_le_of_gt hprev)))
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hh
  linarith

theorem endpoint_upper_index_bounds {L t : ℝ} (ht : 0 < t) {k : ℕ}
    (hk : 1 ≤ k) (h : Real.exp t/4 ≤ upperEndpoint L k)
    (hnext : upperEndpoint L (k+1) < Real.exp t/4) :
    L/(2*t)-1/2 < (k : ℝ) ∧ (k : ℝ) ≤ L/(2*t)+1/2 := by
  refine ⟨?_, (threshold_le_upperEndpoint_iff ht hk).mp h⟩
  have hh := (not_le.mp (mt (threshold_le_upperEndpoint_iff ht (by omega : 1 ≤ k+1)).mpr
    (not_le_of_gt hnext)))
  rw [Nat.cast_add, Nat.cast_one] at hh
  linarith



def lowerIndex (A : ℝ) : ℕ := ⌈A+1/2⌉₊
def upperIndex (B : ℝ) (offset : ℕ) : ℕ := ⌊B+1/2⌋₊ - offset

theorem lowerIndex_bounds {A : ℝ} (hA : 0 ≤ A) :
    A+1/2 ≤ (lowerIndex A : ℝ) ∧ (lowerIndex A : ℝ) < A+3/2 := by
  unfold lowerIndex
  exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ A+1/2)]⟩

theorem upperIndex_bounds {B : ℝ} (hB : 2 ≤ B) {offset : ℕ} (ho : offset ≤ 1) :
    B-(offset : ℝ)-1/2 < (upperIndex B offset : ℝ) ∧
      (upperIndex B offset : ℝ) ≤ B-(offset : ℝ)+1/2 := by
  have hf : offset ≤ ⌊B+1/2⌋₊ := by
    apply Nat.le_floor
    have hoR : (offset : ℝ) ≤ 1 := by exact_mod_cast ho
    linarith
  unfold upperIndex
  rw [Nat.cast_sub hf]
  have hl := Nat.floor_le (by linarith : 0 ≤ B+1/2)
  have hu := Nat.lt_floor_add_one (B+1/2)
  constructor <;> linarith

theorem rounded_pair_bounds {A B : ℝ} (hA : 2 ≤ A) (hB : 4*A ≤ B)
    {offset : ℕ} (ho : offset ≤ 1) :
    1 ≤ lowerIndex A ∧ lowerIndex A ≤ upperIndex B offset ∧
      (lowerIndex A : ℝ) ≤ 2*A ∧ B/2 ≤ (upperIndex B offset : ℝ)+1 ∧
      (upperIndex B offset : ℝ)+1 ≤ 2*B := by
  have ha := lowerIndex_bounds (by linarith : 0 ≤ A)
  have hb := upperIndex_bounds (by linarith : 2 ≤ B) ho
  have hoR : (offset : ℝ) ≤ 1 := by exact_mod_cast ho
  have ho0 : (0 : ℝ) ≤ offset := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ lowerIndex A := by linarith
  have hab : (lowerIndex A : ℝ) ≤ upperIndex B offset := by linarith
  refine ⟨by exact_mod_cast h1, by exact_mod_cast hab, ?_, ?_, ?_⟩ <;> linarith

theorem lowerIndex_endpoint {L t A : ℝ} (ht : 0 < t) (hA : 2 ≤ A)
    (heq : L/(2*t) = A) :
    upperEndpoint L (lowerIndex A) ≤ Real.exp t/4 ∧
      Real.exp t/4 < upperEndpoint L (lowerIndex A-1) := by
  have ha := lowerIndex_bounds (by linarith : 0 ≤ A)
  have hk : 2 ≤ lowerIndex A := by exact_mod_cast (show (2 : ℝ) ≤ lowerIndex A by linarith)
  refine ⟨(upperEndpoint_le_threshold_iff ht (by omega)).mpr (by rw [heq]; exact ha.1), ?_⟩
  apply lt_of_not_ge
  intro h
  have hh := (upperEndpoint_le_threshold_iff ht (by omega : 1 ≤ lowerIndex A-1)).mp h
  rw [heq, Nat.cast_sub (by omega : 1 ≤ lowerIndex A), Nat.cast_one] at hh
  linarith

theorem upperIndex_endpoint {L t B : ℝ} (ht : 0 < t) (hB : 2 ≤ B)
    (heq : L/(2*t) = B) {offset : ℕ} (ho : offset ≤ 1) :
    Real.exp t/4 ≤ upperEndpoint L (upperIndex B offset+offset) ∧
      upperEndpoint L (upperIndex B offset+offset+1) < Real.exp t/4 := by
  have hb := upperIndex_bounds hB ho
  have hk : 1 ≤ upperIndex B offset+offset := by
    have hh : (1 : ℝ) ≤ (upperIndex B offset : ℝ)+(offset : ℝ) := by linarith
    exact_mod_cast hh
  refine ⟨(threshold_le_upperEndpoint_iff ht hk).mpr ?_, ?_⟩
  · rw [heq, Nat.cast_add]
    linarith
  · apply lt_of_not_ge
    intro h
    have hh := (threshold_le_upperEndpoint_iff ht (by omega : 1 ≤ upperIndex B offset+offset+1)).mp h
    rw [heq, Nat.cast_add, Nat.cast_add, Nat.cast_one] at hh
    linarith

end NField.Alignment.KorolevEndpointIndices
