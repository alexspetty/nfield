/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlockGrowth
import NField.Alignment.HarperGaussianInterval
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Uniform accumulation of the source relative errors

A finite product of ratios close to one is controlled by the sum of its
individual errors. Reversed prime-block growth makes that sum geometric
in the first endpoint, uniformly in the number of blocks.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRelativeProducts
open scoped BigOperators Topology
open Filter HarperPrimeBlocks HarperPrimeBlockGrowth HarperGaussianInterval

theorem finite_relative_product_error {ι : Type*} (S : Finset ι)
    (A B e : ι → ℝ) (he : ∀ i ∈ S, 0 ≤ e i)
    (herr : ∀ i ∈ S, |A i/B i-1| ≤ e i) (hsum : ∑ i ∈ S, e i ≤ 1) :
    |(∏ i ∈ S, A i)/(∏ i ∈ S, B i)-1| ≤ 2*∑ i ∈ S, e i := by
  have he0 : 0 ≤ ∑ i ∈ S, e i := Finset.sum_nonneg he
  have hnorm := S.norm_prod_one_add_sub_one_le (fun i => A i/B i-1)
  have hs : ∑ i ∈ S, |A i/B i-1| ≤ ∑ i ∈ S, e i := Finset.sum_le_sum herr
  have hexp := Real.abs_exp_sub_one_le
    (show |∑ i ∈ S, e i| ≤ 1 by rwa [abs_of_nonneg he0])
  have hid (z : ℝ) : 1+(z-1) = z := by ring
  calc
    _ ≤ Real.exp (∑ i ∈ S, |A i/B i-1|)-1 := by
      simpa only [hid, Finset.prod_div_distrib, Real.norm_eq_abs] using hnorm
    _ ≤ Real.exp (∑ i ∈ S, e i)-1 := sub_le_sub_right (Real.exp_le_exp.mpr hs) 1
    _ ≤ 2*∑ i ∈ S, e i := by
      simpa only [abs_of_nonneg he0] using (le_abs_self _).trans hexp

theorem finite_shifted_geometric_sum {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (n : ℕ) :
    (∑ i : Fin n, q^(i.val+1)) ≤ 2*q := by
  have hsum : (∑ i : Fin n, q^i.val) ≤ 2 := by
    calc
      _ ≤ ∑ i : Fin n, (1/(2 : ℝ))^i.val := Finset.sum_le_sum
        (fun i _ => pow_le_pow_left₀ hq0 hq i.val)
      _ ≤ 2 := by simpa only [Fin.sum_univ_eq_sum_range] using sum_geometric_two_le n
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hsum hq0

theorem reversed_block_error_geometric {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) (i : Fin (n+1)) :
    (blockUpper x (l i))^(-(1/100 : ℝ)) ≤
      ((blockUpper x (l 0))^(-(1/100 : ℝ)))^(i.val+1) := by
  have hX : 0 < blockUpper x (l 0) := by linarith [blockUpper_gt_one hx (l 0)]
  have hg : (blockUpper x (l 0))^((i.val : ℝ)+1) ≤ blockUpper x (l i) :=
    (Real.rpow_le_rpow_of_exponent_le (blockUpper_gt_one hx (l 0)).le
      (Real.add_one_le_exp _)).trans (reversed_block_growth hx.le hl i)
  calc
    _ ≤ ((blockUpper x (l 0))^((i.val : ℝ)+1))^(-(1/100 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX _) hg (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le]
      congr 1
      push_cast
      ring

theorem reversed_block_error_sum {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hq : (blockUpper x (l 0))^(-(1/100 : ℝ)) ≤ 1/2) :
    (∑ i : Fin (n+1), intervalComparisonConstant*(blockUpper x (l i))^(-(1/100 : ℝ))) ≤
      2*intervalComparisonConstant*(blockUpper x (l 0))^(-(1/100 : ℝ)) := by
  have hK := intervalComparisonConstant_pos.le
  calc
    _ ≤ ∑ i : Fin (n+1), intervalComparisonConstant*
        ((blockUpper x (l 0))^(-(1/100 : ℝ)))^(i.val+1) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (reversed_block_error_geometric hx hl i) hK)
    _ = intervalComparisonConstant*∑ i : Fin (n+1),
        ((blockUpper x (l 0))^(-(1/100 : ℝ)))^(i.val+1) := by rw [Finset.mul_sum]
    _ ≤ intervalComparisonConstant*(2*(blockUpper x (l 0))^(-(1/100 : ℝ))) :=
      mul_le_mul_of_nonneg_left (finite_shifted_geometric_sum
        (Real.rpow_nonneg (by linarith [blockUpper_gt_one hx (l 0)]) _) hq _) hK
    _ = _ := by ring

theorem eventual_error_sum_scale :
    ∀ᶠ X : ℝ in atTop, X^(-(1/100 : ℝ)) ≤ 1/2 ∧
      2*intervalComparisonConstant*X^(-(1/100 : ℝ)) ≤ 1 := by
  have hp := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)
  have hs : Tendsto (fun X : ℝ => 2*intervalComparisonConstant*X^(-(1/100 : ℝ)))
      atTop (𝓝 0) := by
    simpa using hp.const_mul (2*intervalComparisonConstant)
  filter_upwards [hp.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2),
    hs.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with X hq he
  exact ⟨hq.le,he.le⟩

end NField.Alignment.HarperRelativeProducts
