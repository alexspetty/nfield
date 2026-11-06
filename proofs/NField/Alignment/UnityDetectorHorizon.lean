/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityPrescribedDetectors

/-! # The actual positive logarithmic shallow horizon -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityDetectorHorizon
open UnityNativeHilbert UnityNativeProjection UnityPrescribedDetectors

theorem horizon_ratio_ge_two (N : ℕ) : 2≤Real.log (4/deficit N)/Real.log 2 := by
  have hD := deficit_pos N
  have h1 := deficit_le_one N
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (4:ℝ)≤4/deficit N := (le_div_iff₀ hD).mpr (by nlinarith)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<4) h4
  have he : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 from by norm_num, Real.log_pow]
    norm_num
  rw [he] at hl
  exact (le_div_iff₀ hlog2).mpr hl

theorem horizon_ge_two (N : ℕ) : 2≤horizon N := by
  have h := (horizon_ratio_ge_two N).trans (Nat.le_ceil (Real.log (4/deficit N)/Real.log 2))
  exact_mod_cast h

/-- Title: `The shallow horizon equals the printed integer ceiling`.

 The natural horizon is exactly the integer ceiling printed in the manuscript. -/
theorem horizon_integer_ceiling (N : ℕ) :
    (horizon N : ℤ)=⌈Real.log (4/deficit N)/Real.log 2⌉ :=
  Int.natCast_ceil_eq_ceil (by linarith [horizon_ratio_ge_two N])

theorem zero_depth_eligible {N : ℕ} (hN : 2≤N) : 0∈eligible N := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by have := horizon_ge_two N; omega), ?_⟩
  simpa [coarseCutoff] using hN

/-- Title: `Every published cutoff admits the initial detector depth`. -/
theorem eligible_nonempty {N : ℕ} (hN : 2≤N) : (eligible N).Nonempty :=
  ⟨0, zero_depth_eligible hN⟩

end NField.Alignment.UnityDetectorHorizon
