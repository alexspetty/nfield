/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalLogComparison
import NField.Alignment.ReciprocalFirstDerivativeBound

/-! # The bounded logarithmic range of the reciprocal-prefix estimate -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalBoundedLogPrefix
open scoped BigOperators
open ReciprocalWeightedBlocks ReciprocalLogComparison

def boundedConstant : ℝ := Real.exp ((4096:ℝ)^3)

theorem boundedConstant_pos : 0 < boundedConstant := Real.exp_pos _

theorem reciprocal_prefix_trivial (p M : ℕ) (Q : ℝ) (hM : M ≤ p) :
    ‖reciprocalPrefix p M Q‖ ≤ (p:ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range M, ‖reciprocalPhase Q (p+i+1)‖ := norm_sum_le _ _
    _ = (M:ℝ) := by
      have hnorm (i : ℕ) : ‖reciprocalPhase Q (p+i+1)‖ = 1 := Circle.norm_coe _
      simp only [hnorm,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    _ ≤ _ := by exact_mod_cast hM

theorem log_ge_one_of_four_le (Q : ℝ) (hQ : 4 ≤ Q) : 1 ≤ Real.log Q := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  norm_num at h2
  have h4 : (1:ℝ) ≤ Real.log 4 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  exact h4.trans (Real.log_le_log (by norm_num) hQ)

theorem bounded_log_prefix (p M : ℕ) (Q : ℝ) (hp : 4 ≤ p) (hM : M ≤ p)
    (hQ : 4 ≤ Q) (hL : Real.log (p:ℝ) ≤ 4096) :
    ‖reciprocalPrefix p M Q‖ ≤ boundedConstant*(p:ℝ)*
      Real.exp (-prefixDecay*(Real.log (p:ℝ))^3/(Real.log Q)^2) := by
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hLp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hQlog := log_ge_one_of_four_le Q hQ
  have hQsq : (1:ℝ) ≤ (Real.log Q)^2 := by nlinarith
  have hγ0 : 0 ≤ prefixDecay := prefixDecay_pos.le
  let T := prefixDecay*(Real.log (p:ℝ))^3/(Real.log Q)^2
  have hT : T ≤ (4096:ℝ)^3 := by
    calc
      _ ≤ prefixDecay*(Real.log (p:ℝ))^3 := div_le_self (by positivity) hQsq
      _ ≤ (Real.log (p:ℝ))^3 := by
        have h := mul_le_mul_of_nonneg_right prefixDecay_le_one (pow_nonneg hLp 3)
        simpa only [one_mul] using h
      _ ≤ _ := pow_le_pow_left₀ hLp hL 3
  have hex : 1 ≤ boundedConstant*Real.exp (-T) := by
    dsimp [boundedConstant]
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hex hp0
  apply (reciprocal_prefix_trivial p M Q hM).trans
  calc
    _ ≤ (p:ℝ)*(boundedConstant*Real.exp (-T)) := by simpa only [mul_one] using hmul
    _ = _ := by dsimp [T]; ring

end NField.Alignment.ReciprocalBoundedLogPrefix
