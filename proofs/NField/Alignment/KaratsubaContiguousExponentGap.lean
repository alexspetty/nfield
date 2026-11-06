/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceExponentGap

/-! # The exponent margin at the lower edge of a full contiguous prime step -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaContiguousExponentGap

/-- The lower contiguous endpoint contributes one half minus this exact rational loss. -/
theorem contiguous_endpoint_exponent (s : ℝ) (hs : 0 ≤ s) :
    s/(2*s+1) = 1/2-1/(2*(2*s+1)) := by
  let d := 2*s+1
  have hd : d ≠ 0 := by dsimp [d]; linarith
  have he : s/d+1/(2*d) = (1/2 : ℝ) := by
    calc
      _ = s/d+(1/2)/d := by rw [div_div]
      _ = (s+1/2)/d := (add_div _ _ _).symm
      _ = 1/2 := (div_eq_div_iff hd (by norm_num : (2 : ℝ) ≠ 0)).mpr (by dsimp [d]; ring)
  change s/d = 1/2-1/(2*d)
  linarith

/-- Even the lower edge of the full contiguous step leaves a positive source exponent margin. -/
theorem contiguous_exponent_gap {k s : ℝ} (hk : 1 ≤ k) (hsep : 8*k^2 ≤ s) :
    1/(64*k^2) ≤ k*(2*k/((2*k-1)*(2*k+1))) + s/(2*s+1)-1-1/(2*s-1) := by
  have hk0 : 0 < k := by linarith
  have hs : 8 ≤ s := by nlinarith [sq_nonneg (k-1)]
  have hs0 : 0 < s := by linarith
  rw [KaratsubaSourceExponentGap.lower_endpoint_exponent k hk,
    contiguous_endpoint_exponent s hs0.le]
  have hf : 1/(8*k^2) ≤ 1/(2*(4*k^2-1)) := by
    apply one_div_le_one_div_of_le (by nlinarith : 0 < 2*(4*k^2-1))
    nlinarith
  have hquarter : 1/(2*(2*s+1)) ≤ 1/(4*s) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 4*s)
    linarith
  have hu : 1/(2*s-1) ≤ 3/(5*s) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 2*s-1) (by positivity : 0 < 5*s)).mpr
    linarith
  have hfrac : 17/(20*s) ≤ 17/(160*k^2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 17) (by positivity : 0 < 160*k^2)
    nlinarith only [hsep]
  have he : 1/(4*s)+3/(5*s) = 17/(20*s) := by ring
  have hd : 1/(8*k^2)-17/(160*k^2)-1/(64*k^2) = 1/(320*k^2) := by ring
  have hp : 0 ≤ 1/(320*k^2) := by positivity
  linarith

end NField.Alignment.KaratsubaContiguousExponentGap
