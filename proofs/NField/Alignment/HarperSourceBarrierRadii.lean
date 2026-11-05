/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPathSuffix

/-!
# Comparison radii after an amplitude-sized prefix

Reversed block growth supplies a linear lower bound for every comparison
radius. The exact suffix barriers fit this radius once the prefix length
is within one of the amplitude. Logarithmic time translation costs only
a fixed multiple of the amplitude.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSourceBarrierRadii
open HarperPrimeBlocks HarperPrimeBlockGrowth

theorem exp_ge_quarter_square {s : ℝ} (hs : 0 ≤ s) :
    (s+1)^2/4 ≤ Real.exp s := by
  have he := Real.add_one_le_exp (s/2)
  have hid : Real.exp s = (Real.exp (s/2))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith [sq_nonneg s,Real.exp_pos (s/2)]

theorem source_radius_linear {x K : ℝ} (hx : 1 < x) (hK : 0 ≤ K) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hfirst : (160*K)^2 ≤ Real.log (blockUpper x (l 0))) (i : Fin (n+1)) :
    K*((i.val : ℝ)+1) ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80 := by
  have he := exp_ge_quarter_square (Nat.cast_nonneg (α := ℝ) i.val)
  have hg := reversed_block_log_growth hx hl i
  have hm := mul_le_mul_of_nonneg_left hfirst (Real.exp_nonneg (i.val : ℝ))
  have he' := mul_le_mul_of_nonneg_right he (sq_nonneg (160*K))
  have hsq : (80*(K*((i.val : ℝ)+1)))^2 ≤ Real.log (blockUpper x (l i)) := by
    nlinarith
  have hroot := Real.sq_sqrt (Real.log_pos (blockUpper_gt_one hx (l i))).le
  have hnon := Real.sqrt_nonneg (Real.log (blockUpper x (l i)))
  have hleft : 0 ≤ 80*(K*((i.val : ℝ)+1)) := by positivity
  nlinarith

theorem log_add_le_log_prefix_add_log {p r : ℝ} (hp : 0 ≤ p) (hr : 1 ≤ r) :
    Real.log (p+r) ≤ p+Real.log r := by
  have hr0 : 0 < r := by linarith
  have hp1 : 0 < p+1 := by linarith
  calc
    _ ≤ Real.log ((p+1)*r) := Real.log_le_log (by linarith) (by nlinarith)
    _ = Real.log (p+1)+Real.log r := Real.log_mul (ne_of_gt hp1) (ne_of_gt hr0)
    _ ≤ _ := add_le_add (by simpa using Real.log_le_sub_one_of_pos hp1) le_rfl

theorem suffix_lower_radius {a b p r : ℝ} (hb : 0 ≤ b) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (ha : a ≤ p+1) :
    -(b+20)*(p+r) ≤ (-a-b*(p+r))-(a+p+10*Real.log p) := by
  have hlog : Real.log p ≤ p := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hbr : 0 ≤ b*r := mul_nonneg hb (by linarith)
  nlinarith

theorem suffix_upper_radius {a b p r : ℝ} (hb : 0 ≤ b) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (ha : a ≤ p+1) :
    (a+(p+r)+10*Real.log (p+r))-(-a-b*p) ≤ (b+20)*(p+r) := by
  have hlog : Real.log (p+r) ≤ p+r :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hbr : 0 ≤ b*r := mul_nonneg hb (by linarith)
  nlinarith

theorem suffix_upper_logarithmic {a b p r : ℝ} (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hr : 1 ≤ r) (hpa : p ≤ a) :
    (a+(p+r)+10*Real.log (p+r))-(-a-b*p) ≤ r+(b+13)*a+10*Real.log r := by
  have hlog := log_add_le_log_prefix_add_log hp hr
  have hm := mul_le_mul_of_nonneg_left hpa hb
  nlinarith

end NField.Alignment.HarperSourceBarrierRadii
