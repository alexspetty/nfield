/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalDyadicPartition

/-! # Conditional real reciprocal distribution theorem
The uniform real reciprocal cancellation estimate is retained as a premise.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalDistributionConditional
open ReciprocalWeightedBlocks ReciprocalBlockDiscrepancy ReciprocalOptimizedBlock
  ReciprocalFourierCutoff ReciprocalDyadicDecay ReciprocalDyadicPartition
open scoped BigOperators Classical

/-- Natural-endpoint specialization needed from the real reciprocal estimate(R).
This predicate is a hypothesis, not an asserted analytic theorem. -/
def ReciprocalPrefixEstimate (C γ : ℝ) : Prop :=
  ∀ p M : ℕ, ∀ Q : ℝ, 4 ≤ p → M ≤ p → 4 ≤ Q →
    ‖reciprocalPrefix p M Q‖ ≤
      C*((p : ℝ)*Real.exp (-γ*(Real.log p)^3/(Real.log Q)^2)+(p : ℝ)^2/Q)

/-- Exact dyadic reassembly of the full centered distribution, conditional
on the uniform real reciprocal-prefix estimate. -/
theorem centered_distribution_bound (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hR : ReciprocalPrefixEstimate C γ) (Y : ℕ) (hY : 0 < Y) (x α : ℝ)
    (hx : 4 ≤ x) (hYx : (Y : ℝ) ≤ x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) Y| ≤
      4+(8+8*C)*((2+1/(γ*(Real.log 2)^3/16))*(Real.rpow (Real.log x) (2/3 : ℝ)+1)+4) := by
  let K := 8+8*C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb (j : ℕ) :
      |blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j)| ≤
        K*(Real.exp (-γ*(Real.log (start j))^3/(16*(Real.log x)^2))+(start j : ℝ)/x) := by
    by_cases hz : length Y j = 0
    · simp only [hz, blockDistribution, FejerWeightedDiscrepancy.thresholdSum, blockMass,
        Finset.range_zero, Finset.sum_empty, mul_zero, sub_self, abs_zero]
      positivity
    · have hp4 : 4 ≤ start j := by
        have hh : 0 < (2 : ℕ)^j := by positivity
        unfold start
        omega
      have hpY : start j < Y := by
        unfold length at hz
        omega
      have hpx : (start j : ℝ) ≤ x := (by exact_mod_cast hpY.le : (start j : ℝ) ≤ Y).trans hYx
      have hpref : ∀ h ∈ Finset.Icc 1 (cutoff (γ*(Real.log (start j))^3/(16*(Real.log x)^2))),
          ∀ n ≤ length Y j, ‖reciprocalPrefix (start j) n ((h : ℝ)*x)‖ ≤
            C*((start j : ℝ)*Real.exp (-γ*(Real.log (start j))^3/(Real.log ((h : ℝ)*x))^2)+
              (start j : ℝ)^2/((h : ℝ)*x)) := by
        intro h hh n hn
        have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
        exact hR _ _ _ hp4 (hn.trans (length_le_start Y j)) (by nlinarith)
      have hob := optimized_block (start j) (length Y j) (by omega)
        ((length_le_start Y j).trans (Nat.le_succ _)) x α C γ (by linarith) hpx hC hγ.le hγ1 hα0 hα1 hpref
      simpa only [K, neg_div, neg_mul] using hob
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (Nat.log 2 Y)) => hb j)
  have heq : (∑ j ∈ Finset.range (Nat.log 2 Y),
      K*(Real.exp (-γ*(Real.log (start j))^3/(16*(Real.log x)^2))+(start j : ℝ)/x)) =
      K*((∑ j ∈ Finset.range (Nat.log 2 Y), Real.exp (-γ*(Real.log (start j))^3/(16*(Real.log x)^2)))+
        ∑ j ∈ Finset.range (Nat.log 2 Y), (start j : ℝ)/x) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  rw [heq] at hs
  have hd := dyadic_decay_sum γ (Real.log x) hγ (Real.log_pos (by linarith)) (Nat.log 2 Y)
  have hd' : (∑ j ∈ Finset.range (Nat.log 2 Y), Real.exp (-γ*(Real.log (start j))^3/(16*(Real.log x)^2))) ≤
      (2+1/(γ*(Real.log 2)^3/16))*(Real.rpow (Real.log x) (2/3 : ℝ)+1) := by
    simpa only [start, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hd
  have hl := dyadic_start_cost Y hY x (by linarith)
  have hl4 : 4*(Y : ℝ)/x ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < x)).mpr
    linarith
  have ha := centered_error_sum Y x α hα0 hα1
  have hm := mul_le_mul_of_nonneg_left (add_le_add hd' (hl.trans hl4)) hK
  dsimp only [K] at *
  linarith

def distributionConstant (C γ : ℝ) : ℝ :=
  4+(8+8*C)*(2*(2+1/(γ*(Real.log 2)^3/16))+4)

theorem centered_distribution_scale (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hR : ReciprocalPrefixEstimate C γ) (Y : ℕ) (hY : 0 < Y) (x α : ℝ)
    (hx : 4 ≤ x) (hYx : (Y : ℝ) ≤ x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) Y| ≤
      distributionConstant C γ * Real.rpow (Real.log x) (2/3 : ℝ) := by
  have hb := centered_distribution_bound C γ hC hγ hγ1 hR Y hY x α hx hYx hα0 hα1
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr
    (Real.exp_one_lt_three.le.trans (by linarith))
  have hr := Real.one_le_rpow hl (by norm_num : (0 : ℝ) ≤ 2/3)
  have hr' : 1 ≤ Real.rpow (Real.log x) (2/3 : ℝ) := by
    simpa only [Real.rpow_eq_pow] using hr
  let D := 2+1/(γ*(Real.log 2)^3/16)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ 8+8*C := by positivity
  have hd := mul_le_mul_of_nonneg_left (show Real.rpow (Real.log x) (2/3 : ℝ)+1 ≤
      2*Real.rpow (Real.log x) (2/3 : ℝ) by linarith) hD
  have hm := mul_le_mul_of_nonneg_left
    (show D*(Real.rpow (Real.log x) (2/3 : ℝ)+1)+4 ≤
      (2*D+4)*Real.rpow (Real.log x) (2/3 : ℝ) by nlinarith) hK
  unfold distributionConstant
  dsimp only [D] at hm
  nlinarith

end NField.Alignment.ReciprocalDistributionConditional
