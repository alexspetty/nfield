/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevIndexSeparation

/-! # The positive exponent gap in the source prime-window parameters -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourceExponentGap

/-- The exact lower-endpoint contribution exceeds one half by its rational correction. -/
theorem lower_endpoint_exponent (t : ℝ) (ht : 1 ≤ t) :
    t*(2*t/((2*t-1)*(2*t+1))) = 1/2 + 1/(2*(4*t^2-1)) := by
  let d := (2*t-1)*(2*t+1)
  have hd : d ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hd2 : 2*d ≠ 0 := mul_ne_zero (by norm_num) hd
  have hid : 4*t^2-1 = d := by dsimp [d]; ring
  have hsplit : (d+1)/(2*d) = 1/2 + 1/(2*d) := by
    rw [add_div]
    congr 1
    apply (div_eq_div_iff hd2 (by norm_num : (2 : ℝ) ≠ 0)).mpr
    ring
  rw [hid, ← hsplit, ← mul_div_assoc]
  apply (div_eq_div_iff hd hd2).mpr
  dsimp [d]
  ring

/-- Square separation leaves a strict power margin after the full ordinary-coordinate width. -/
theorem exponent_gap {k s : ℝ} (hk : 1 ≤ k) (hsep : 8*k^2 ≤ s) :
    1/(24*k^2) ≤
      k*(2*k/((2*k-1)*(2*k+1))) + s*(2*s/((2*s-1)*(2*s+1))) -
        1 - 1/(2*s-1) := by
  have hs : 1 ≤ s := by nlinarith [sq_nonneg (k-1)]
  rw [lower_endpoint_exponent k hk, lower_endpoint_exponent s hs]
  have hp : 0 < 2*(4*k^2-1) := by nlinarith
  have hf : 1/(8*k^2) ≤ 1/(2*(4*k^2-1)) := by
    apply one_div_le_one_div_of_le hp
    nlinarith
  have hk2 : 0 < 12*k^2 := by positivity
  have hu : 1/(2*s-1) ≤ 1/(12*k^2) := by
    apply one_div_le_one_div_of_le hk2
    nlinarith [sq_nonneg (k-1)]
  have hsp : 0 < 2*(4*s^2-1) := by nlinarith
  have hb : 0 ≤ 1/(2*(4*s^2-1)) := one_div_nonneg.mpr hsp.le
  have he : 1/(8*k^2)-1/(12*k^2) = 1/(24*k^2) := by ring
  linarith

/-- The actual rounded source indices supply the positive exponent gap. -/
theorem selected_exponent_gap {v u c : ℝ} (hB : 2 ≤ KorolevSourceScales.pStop v u c)
    {k s : ℕ} (hk : 1 ≤ k) (hklast : k ≤ KorolevWindowParameters.pLast v u c)
    (hsfirst : KorolevWindowParameters.qFirst v u c ≤ s) :
    1/(24*(k : ℝ)^2) ≤
      (k : ℝ)*(2*(k : ℝ)/((2*(k : ℝ)-1)*(2*(k : ℝ)+1))) +
        (s : ℝ)*(2*(s : ℝ)/((2*(s : ℝ)-1)*(2*(s : ℝ)+1))) -
          1 - 1/(2*(s : ℝ)-1) := by
  apply exponent_gap (by exact_mod_cast hk)
  exact KorolevIndexSeparation.selected_index_separation hB hklast hsfirst

end NField.Alignment.KaratsubaSourceExponentGap
