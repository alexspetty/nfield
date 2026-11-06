/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The native reciprocal weights

These are the actual weights `1 / (m * (m + 1))` of the published Unity
paper, with value zero at `m = 0`. No replacement by Haar measure is made.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityNativeWeights
open scoped BigOperators
open Filter Topology

/-- The positive-integer native weight, extended by zero at the origin. -/
def weight (m : ℕ) : ℝ := 1 / ((m : ℝ) * (m + 1))

@[simp] theorem weight_zero : weight 0 = 0 := by simp [weight]

theorem weight_nonneg (m : ℕ) : 0 ≤ weight m := by unfold weight; positivity

theorem weight_pos {m : ℕ} (hm : 0 < m) : 0 < weight m := by
  unfold weight
  exact one_div_pos.mpr (mul_pos (by exact_mod_cast hm) (by positivity))

theorem weight_difference {m : ℕ} (hm : 0 < m) :
    weight m = (m : ℝ)⁻¹ - ((m : ℝ) + 1)⁻¹ := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold weight
  field_simp
  ring

theorem sum_weights (M : ℕ) :
    (∑ n ∈ Finset.range M, weight (n + 1)) = 1 - ((M : ℝ) + 1)⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, weight_difference (by omega)]
    push_cast
    ring

theorem weights_hasSum : HasSum (fun n : ℕ => weight (n + 1)) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => weight_nonneg (n+1)) 1).mpr
  have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun M : ℕ => 1 / ((M : ℝ) + 1)) atTop (𝓝 0))
  have he := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub ht
  simpa only [sum_weights, sub_zero] using he

theorem weights_summable : Summable (fun n : ℕ => weight (n + 1)) :=
  weights_hasSum.summable

/-- Title: `Native reciprocal weights have total mass one`. -/
@[simp] theorem weights_tsum : (∑' n : ℕ, weight (n + 1)) = 1 := weights_hasSum.tsum_eq

/-- The exact mass of a finite interval, including every endpoint weight. -/
theorem weight_block (a L : ℕ) (ha : 0 < a) :
    (∑ i ∈ Finset.range L, weight (a + i)) =
      (a : ℝ)⁻¹ - ((a : ℝ) + L)⁻¹ := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, weight_difference (by omega)]
    push_cast
    ring

/-- Title: `Complete integer blocks have reciprocal mass`.

 Complete integer copies have exactly reciprocal mass. -/
theorem copy_block_weight (b m : ℕ) (hb : 0 < b) (hm : 0 < m) :
    (∑ i ∈ Finset.range b, weight (b*m+i)) = weight m / b := by
  rw [weight_block (b*m) b (Nat.mul_pos hb hm)]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hprod : (b : ℝ)*(m : ℝ)+(b : ℝ) ≠ 0 := by positivity
  unfold weight
  push_cast
  field_simp
  ring

end NField.Alignment.UnityNativeWeights
