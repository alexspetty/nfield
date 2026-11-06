/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProgressionMertens
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # The ordinary real-cutoff Mertens progression limit -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ProgressionMertens

open Filter Asymptotics
open scoped Topology

theorem equivalent_log_difference_tendsto {f g : ℝ → ℝ}
    (hfg : f ~[atTop] g) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x => Real.log (f x) - Real.log (g x)) atTop (𝓝 0) := by
  have hf := hfg.symm.tendsto_atTop hg
  have hratio := (isEquivalent_iff_tendsto_one (hg.eventually_ne_atTop 0)).mp hfg
  have hlog := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hlog
  apply hlog.congr'
  filter_upwards [hf.eventually_ne_atTop 0, hg.eventually_ne_atTop 0] with x hx hy
  exact Real.log_div hx hy

theorem log_log_floor_difference_tendsto :
    Tendsto (fun x : ℝ => Real.log (Real.log (⌊x⌋₊ : ℝ)) -
      Real.log (Real.log x)) atTop (𝓝 0) := by
  exact equivalent_log_difference_tendsto
    ((Asymptotics.isEquivalent_nat_floor (R := ℝ)).log tendsto_id)
    Real.tendsto_log_atTop

/-- Title: `Real cutoff Mertens progression limit`.
This is the exact classical fixed-modulus input used by the collision papers. -/
theorem real_cutoff_mertens_progression {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    ∃ L : ℝ, Tendsto (fun x : ℝ =>
      realProgressionPrimeSum a ⌊x⌋₊ - Real.log (Real.log x) / (q.totient : ℝ))
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := realProgressionPrimeSum_residual_tendsto ha
  have hbase := hL.comp (show Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop from
    tendsto_nat_floor_atTop)
  have hdiff := log_log_floor_difference_tendsto.div_const (q.totient : ℝ)
  have h := hbase.add hdiff
  simp only [zero_div, add_zero] at h
  refine ⟨L, ?_⟩
  convert h using 1
  ext x
  simp only [Function.comp_apply]
  ring

end NField.Alignment.ProgressionMertens
