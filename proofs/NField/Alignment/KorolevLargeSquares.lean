/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperIntervalSieve
import Mathlib.Analysis.PSeries

/-!
# Actual large-square exclusion

Count positive integers n<=x divisible by some l^2 with l>y. Exact
multiple counts and the finite reciprocal-square tail give 2*x/y.
No density assumption or squarefree decomposition is used in this count.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevLargeSquares
open HarperIntervalSieve
open scoped BigOperators Classical

def largeSquareSet (x y : ℝ) : Finset ℕ :=
  (intervalSupport 0 x).filter (fun n => ∃ l : ℕ, y < (l : ℝ) ∧ l^2 ∣ n)

theorem largeSquareSet_mem {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) :
    n ∈ largeSquareSet x y ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ ∃ l : ℕ, y < (l : ℝ) ∧ l^2 ∣ n := by
  rw [largeSquareSet, Finset.mem_filter, intervalSupport_mem (by norm_num) hx]
  norm_cast
  tauto

theorem square_multiple_count {x : ℝ} (hx : 0 ≤ x) {l : ℕ} (hl : 0 < l) :
    (((intervalSupport 0 x).filter (fun n => l^2 ∣ n)).card : ℝ) ≤ x/(l : ℝ)^2 := by
  rw [intervalSupport, Nat.floor_zero, Nat.Ioc_filter_dvd_card_eq_div,
    ← Nat.floor_div_natCast, Nat.cast_pow]
  exact Nat.floor_le (by positivity)

theorem large_square_count {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    ((largeSquareSet x y).card : ℝ) ≤ 2*x/y := by
  let indices := Finset.Ioo ⌊y⌋₊ (⌊x⌋₊+1)
  let multiples := fun l : ℕ => (intervalSupport 0 x).filter (fun n => l^2 ∣ n)
  have hcover : largeSquareSet x y ⊆ indices.biUnion multiples := by
    intro n hn
    obtain ⟨hn0, hnx, l, hyl, hln⟩ := (largeSquareSet_mem hx y n).mp hn
    have hld : l ∣ n := dvd_trans (show l ∣ l^2 from ⟨l, by ring⟩) hln
    have hlx : l ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr
      ((by exact_mod_cast Nat.le_of_dvd hn0 hld : (l : ℝ) ≤ n).trans hnx)
    apply Finset.mem_biUnion.mpr
    refine ⟨l, Finset.mem_Ioo.mpr ⟨(Nat.floor_lt hy.le).mpr hyl, by omega⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨(intervalSupport_mem (by norm_num) hx n).mpr
      ⟨by exact_mod_cast hn0, hnx⟩, hln⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcR : ((largeSquareSet x y).card : ℝ) ≤ ∑ l ∈ indices, ((multiples l).card : ℝ) := by
    exact_mod_cast hc
  have hsum := sum_Ioo_inv_sq_le (α := ℝ) ⌊y⌋₊ (⌊x⌋₊+1)
  have hyfloor : y < (⌊y⌋₊ : ℝ)+1 := Nat.lt_floor_add_one y
  calc
    _ ≤ ∑ l ∈ indices, ((multiples l).card : ℝ) := hcR
    _ ≤ ∑ l ∈ indices, x/(l : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact square_multiple_count hx (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioo.mp hl).1)
    _ = x*∑ l ∈ indices, ((l : ℝ)^2)⁻¹ := by simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ x*(2/((⌊y⌋₊ : ℝ)+1)) := mul_le_mul_of_nonneg_left hsum hx
    _ = 2*x/((⌊y⌋₊ : ℝ)+1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hy hyfloor.le

theorem coprime_large_square_count {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (m : ℕ) :
    (((largeSquareSet x y).filter (fun n => n.Coprime m)).card : ℝ) ≤ 2*x/y := by
  have h : (((largeSquareSet x y).filter (fun n => n.Coprime m)).card : ℝ) ≤
      (largeSquareSet x y).card := by
    exact_mod_cast Finset.card_filter_le (largeSquareSet x y) (fun n => n.Coprime m)
  exact h.trans (large_square_count hx hy)

end NField.Alignment.KorolevLargeSquares
