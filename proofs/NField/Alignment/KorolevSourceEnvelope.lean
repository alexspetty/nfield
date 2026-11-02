/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform smallness of the selected-index envelope

Both source index families fit below 4*exp(5*v/12). Its square divided
by exp(v) tends to zero, controlling the finite size condition and both
Mertens errors. No condition on the shorter-sum coordinate u is needed.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceEnvelope
open Filter
open scoped Topology

def envelope (v : ℝ) : ℝ := 4*Real.exp (5*v/12)

theorem envelope_pos (v : ℝ) : 0 < envelope v := by unfold envelope; positivity

theorem envelope_square_ratio (v : ℝ) :
    (envelope v)^2/Real.exp v = 16*Real.exp (-v/6) := by
  unfold envelope
  rw [mul_pow, ← Real.exp_nat_mul, mul_div_assoc, ← Real.exp_sub]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

theorem envelope_square_ratio_tendsto :
    Tendsto (fun v => (envelope v)^2/Real.exp v) atTop (𝓝 0) := by
  simp_rw [envelope_square_ratio]
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1/6))
  have h' := h.const_mul 16
  simpa [Function.comp_def, neg_mul, div_eq_mul_inv, mul_comm] using h'

theorem eventual_envelope_small (K : ℝ) :
    ∀ᶠ v : ℝ in atTop, K*(envelope v)^2/Real.exp v ≤ 1 := by
  have h : Tendsto (fun v => K*(envelope v)^2/Real.exp v) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using envelope_square_ratio_tendsto.const_mul K
  exact h.eventually_le_const (by norm_num : (0 : ℝ) < 1)

theorem eventual_finite_conditions : ∀ᶠ v : ℝ in atTop,
    ∀ b : ℕ, (b : ℝ)+1 ≤ envelope v →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ Real.exp v ∧
      KorolevWindowMass.lossConstant*((b : ℝ)+1)^2/Real.exp v ≤ 1 ∧
      12*KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/Real.exp v ≤ 1 := by
  filter_upwards [eventual_envelope_small (8*(Real.log 4+1)),
    eventual_envelope_small KorolevWindowMass.lossConstant,
    eventual_envelope_small (12*KorolevPrimeIntervals.errorConstant)]
    with v hs hd hc b hb
  have hb0 : 0 ≤ (b : ℝ)+1 := by positivity
  have hsq := pow_le_pow_left₀ hb0 hb 2
  have hsize : 8*(Real.log 4+1)*(envelope v)^2 ≤ Real.exp v :=
    by simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos v)).mp hs
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8*(Real.log 4+1) by positivity)
    nlinarith
  · exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq KorolevWindowMass.lossConstant_pos.le)
      (Real.exp_pos v).le).trans hd
  · have hl : (b : ℝ)+1 ≤ (envelope v)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) b]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num) KorolevPrimeIntervals.errorConstant_pos.le))
      (Real.exp_pos v).le).trans hc

end NField.Alignment.KorolevSourceEnvelope
