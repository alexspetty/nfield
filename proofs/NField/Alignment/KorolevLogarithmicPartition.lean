/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeIntervals
import Mathlib.Order.Interval.Set.Union

/-! # Finite equal-width logarithmic partitions with controlled endpoint ratios -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevLogarithmicPartition
open KorolevPrimeIntervals
open scoped Classical

def blockCount (D A : ℝ) : ℕ := ⌊D/A⌋₊
def width (D A : ℝ) : ℝ := D / blockCount D A
def point (l D A : ℝ) (i : ℕ) : ℝ := Real.exp (l + (i : ℝ)*width D A)
def block (l D A : ℝ) (i : ℕ) : Finset ℕ :=
  intervalPrimes (point l D A i) (point l D A (i+1))

/-- Redistributing the final remainder gives widths in [A,2A) and a count bound. -/
theorem count_width {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) :
    1 ≤ blockCount D A ∧ A ≤ width D A ∧ width D A < 2*A ∧
      (blockCount D A : ℝ) ≤ D/A := by
  have hD0 : 0 ≤ D := by linarith
  have hpos : 0 < blockCount D A := Nat.floor_pos.mpr ((one_le_div hA).mpr hD)
  have hn : (1 : ℝ) ≤ blockCount D A := by exact_mod_cast hpos
  have hn0 : (0 : ℝ) < blockCount D A := by linarith
  have hf : (blockCount D A : ℝ) ≤ D/A := Nat.floor_le (div_nonneg hD0 hA.le)
  have ht : D/A < (blockCount D A : ℝ)+1 := Nat.lt_floor_add_one _
  have hlo : (blockCount D A : ℝ)*A ≤ D := (le_div_iff₀ hA).mp hf
  have hhi : D < ((blockCount D A : ℝ)+1)*A := (div_lt_iff₀ hA).mp ht
  refine ⟨by omega, (le_div_iff₀ hn0).mpr (by nlinarith only [hlo]),
    (div_lt_iff₀ hn0).mpr ?_, hf⟩
  nlinarith [mul_le_mul_of_nonneg_right hn hA.le]

/-- The partition begins at the original lower endpoint. -/
theorem point_zero (l D A : ℝ) : point l D A 0 = Real.exp l := by simp [point]

/-- The partition ends at the original upper endpoint. -/
theorem point_last (l : ℝ) {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) :
    point l D A (blockCount D A) = Real.exp (l+D) := by
  have hn : (blockCount D A : ℝ) ≠ 0 := by exact_mod_cast (by have := (count_width hA hD).1; omega : blockCount D A ≠ 0)
  simp [point, width, mul_div_cancel₀ _ hn]

/-- Every block has the same controlled logarithmic width. -/
theorem log_increment (l D A : ℝ) (i : ℕ) :
    Real.log (point l D A (i+1)) = Real.log (point l D A i) + width D A := by
  simp only [point, Real.log_exp, Nat.cast_add, Nat.cast_one]
  ring

/-- Positive logarithmic widths strictly order the endpoints. -/
theorem point_strictMono (l : ℝ) {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) :
    StrictMono (point l D A) := by
  have hw : 0 < width D A := lt_of_lt_of_le hA (count_width hA hD).2.1
  intro i j hij
  apply Real.exp_lt_exp.mpr
  have hc : (i : ℝ) < j := by exact_mod_cast hij
  simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hc hw) l

/-- The finite prime blocks cover exactly the original interval, including its upper endpoint. -/
theorem biUnion_blocks (l : ℝ) {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) :
    (Finset.range (blockCount D A)).biUnion (block l D A) =
      intervalPrimes (Real.exp l) (Real.exp (l+D)) := by
  have hm := (point_strictMono l hA hD).monotone
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpp, hlo, hhi⟩ := intervalPrimes_mem.mp hp
    apply intervalPrimes_mem.mpr
    refine ⟨hpp, ?_, ?_⟩
    · have h := hm (Nat.zero_le i)
      rw [point_zero] at h
      exact h.trans_lt hlo
    · have h := hm (show i+1 ≤ blockCount D A by have := Finset.mem_range.mp hi; omega)
      rw [point_last l hA hD] at h
      exact hhi.trans h
  · intro hp
    obtain ⟨hpp, hlo, hhi⟩ := intervalPrimes_mem.mp hp
    have hp' : (p : ℝ) ∈ Set.Ioc (point l D A 0) (point l D A (blockCount D A)) := by
      rw [point_zero, point_last l hA hD]
      exact ⟨hlo, hhi⟩
    have hc := Ioc_subset_biUnion_Ioc (blockCount D A) (point l D A) hp'
    simp only [Set.mem_iUnion] at hc
    obtain ⟨i, hi, hpi⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨i, hi, intervalPrimes_mem.mpr ⟨hpp, hpi.1, hpi.2⟩⟩

/-- Distinct prime blocks are disjoint, so later sums carry no multiplicity factor. -/
theorem blocks_disjoint (l : ℝ) {D A : ℝ} (hA : 0 < A) (hD : A ≤ D)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (block l D A i) (block l D A j) := by
  have hm := (point_strictMono l hA hD).monotone
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨_, hli, hui⟩ := intervalPrimes_mem.mp hpi
  obtain ⟨_, hlj, huj⟩ := intervalPrimes_mem.mp hpj
  rcases lt_or_gt_of_ne hij with h | h
  · have hh := hm (show i+1 ≤ j by omega)
    linarith
  · have hh := hm (show j+1 ≤ i by omega)
    linarith

/-- Exact summation over the partition introduces no overcounting. -/
theorem sum_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (l : ℝ)
    {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) :
    ∑ p ∈ intervalPrimes (Real.exp l) (Real.exp (l+D)), f p =
      ∑ i ∈ Finset.range (blockCount D A), ∑ p ∈ block l D A i, f p := by
  rw [← biUnion_blocks l hA hD]
  apply Finset.sum_biUnion
  intro i _ j _ hij
  exact blocks_disjoint l hA hD hij

/-- Every endpoint ratio is bounded by a fixed constant, independently of the source index. -/
theorem point_ratio_bound (l : ℝ) {D A : ℝ} (hA : 0 < A) (hD : A ≤ D) (i : ℕ) :
    point l D A (i+1) ≤ point l D A i * Real.exp (2*A) := by
  have heq : point l D A (i+1) = point l D A i * Real.exp (width D A) := by
    rw [point, point, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (count_width hA hD).2.2.1.le)
    (Real.exp_pos _).le

end NField.Alignment.KorolevLogarithmicPartition
