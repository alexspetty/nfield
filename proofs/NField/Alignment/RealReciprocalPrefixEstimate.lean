/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalLargePrefix
import NField.Alignment.ReciprocalBoundedLogPrefix
import NField.Alignment.ReciprocalDistributionConditional

/-! # The uniform real reciprocal-prefix estimate

The actual finite reciprocal phase is controlled in every range. The
polynomial moment argument, first-derivative range, and bounded range are
combined with absolute constants; no analytic estimate remains a premise.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealReciprocalPrefixEstimate
open ReciprocalWeightedBlocks ReciprocalDistributionConditional
  ReciprocalLargePrefix ReciprocalBoundedLogPrefix ReciprocalLogComparison
  ReciprocalFirstDerivativeBound

theorem reciprocal_prefix_estimate :
    ∃ C : ℝ, 0 < C ∧ ReciprocalPrefixEstimate C prefixDecay := by
  obtain ⟨C,hC,hlarge⟩ := large_log_prefix_decay
  let K := C+boundedConstant+8
  have hB0 : 0 < boundedConstant := boundedConstant_pos
  have hK : 0 < K := by dsimp [K]; linarith
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hKB : boundedConstant ≤ K := by dsimp [K]; linarith
  have hK8 : (8:ℝ) ≤ K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro p M Q hp hM hQ
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hQ0 : 0 < Q := by linarith
  let E := (p:ℝ)*Real.exp (-prefixDecay*(Real.log (p:ℝ))^3/(Real.log Q)^2)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hpq : 0 ≤ (p:ℝ)^2/Q := by positivity
  have extend (c : ℝ) (hc : c ≤ K)
      (hb : ‖reciprocalPrefix p M Q‖ ≤ c*E) :
      ‖reciprocalPrefix p M Q‖ ≤ K*(E+(p:ℝ)^2/Q) := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hc hE0).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK.le))
  by_cases hfirst : 2*Q ≤ (p:ℝ)^2
  · have hb := large_block_prefix p M hp1 hM Q hQ0 hfirst
    calc
      _ ≤ 8*(p:ℝ)^2/Q := hb
      _ = 8*((p:ℝ)^2/Q) := by ring
      _ ≤ K*((p:ℝ)^2/Q) := mul_le_mul_of_nonneg_right hK8 hpq
      _ ≤ K*(E+(p:ℝ)^2/Q) := mul_le_mul_of_nonneg_left (by linarith) hK.le
  by_cases hsmall : Real.log (p:ℝ) ≤ 4096
  · apply extend boundedConstant hKB
    have hb := bounded_log_prefix p M Q hp hM hQ hsmall
    simpa only [E,mul_assoc] using hb
  have hL : 4096 ≤ Real.log (p:ℝ) := by linarith
  have hL0 : 0 < Real.log (p:ℝ) := by linarith
  let ρ := Real.log Q/Real.log (p:ℝ)
  have hρ : 3/2 ≤ ρ := log_ratio_lower p Q hp0 hQ0 hL (by linarith)
  have hlogQ : Real.log Q = ρ*Real.log (p:ℝ) := by
    dsimp [ρ]
    field_simp
  have hb := hlarge p M Q ρ hp1 hM hQ0 hL hρ hlogQ
  have hd := decay_to_logarithmic (Real.log (p:ℝ)) (Real.log Q) ρ hL0 hρ hlogQ
  apply extend C hKC
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ C*(p:ℝ) by positivity)
  simpa only [E,mul_assoc] using hh

end NField.Alignment.RealReciprocalPrefixEstimate
