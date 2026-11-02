/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowParameters
import NField.Alignment.KorolevMissingPrimeDecay

/-!
# Actual selected-prime exclusion counts with the parameter conditions discharged

In source logarithmic coordinates the two actual missing-prime counts
are uniformly O(x*log(log x)*exp(-gain)). The smooth-count remainder
is absorbed, not dropped. The constants and thresholds are independent
of the varying short-range coordinate and of coprime restriction.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevParameterCount
open Filter KorolevSourceScales KorolevWindowParameters KorolevPrimeWindows
  KorolevMissingPrimeCount KorolevMissingPrimeDecay
open scoped Topology BigOperators Classical

def pPrimes (v u c : ℝ) : Finset ℕ := selectedPrimes (Real.exp v) (pFirst v u c) (pLast v u c)
def qPrimes (v u c : ℝ) : Finset ℕ := KorolevPrimeIntervals.intervalPrimes
  (upperEndpoint (Real.exp v) (qLast v u c+1)) (upperEndpoint (Real.exp v) (qFirst v u c))

theorem absorb_count {C x u g : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hu : 1 ≤ u) (hg : g ≤ u) (S : Finset ℕ) (m : ℕ)
    (hmass : g-Real.log 4-1 ≤ ∑ p ∈ S, (1 : ℝ)/p)
    (hcount : (((avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤
      C*(x/(Real.exp u*u)+x*u*Real.exp (-(∑ p ∈ S, (1 : ℝ)/p)))) :
    (((avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤
      (C*(1+Real.exp (Real.log 4+1)))*x*u*Real.exp (-g) := by
  have hu0 : 0 < u := by linarith
  have hxu : x/u ≤ x*u := by
    apply (div_le_iff₀ hu0).mpr
    have hh : 1 ≤ u^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hx]
  have hinv : 1/Real.exp u ≤ Real.exp (-g) := by
    rw [one_div, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsmooth : x/(Real.exp u*u) ≤ x*u*Real.exp (-g) := by
    calc
      _ = (x/u)*(1/Real.exp u) := by ring
      _ ≤ _ := mul_le_mul hxu hinv (by positivity) (mul_nonneg hx hu0.le)
  have hex : Real.exp (-(∑ p ∈ S, (1 : ℝ)/p)) ≤
      Real.exp (Real.log 4+1)*Real.exp (-g) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hsmooth (mul_le_mul_of_nonneg_left hex (mul_nonneg hx hu0.le))) hC
  apply hcount.trans
  convert hh using 1; ring

theorem eventual_window_missing_counts (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v : ℝ in atTop,
      ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ m : ℕ,
        (((avoidSet (Real.exp (Real.exp u)) (pPrimes v u c)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          K*Real.exp (Real.exp u)*u*Real.exp (-gain v u c) ∧
        (((avoidSet (Real.exp (Real.exp u)) (qPrimes v u c)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          K*Real.exp (Real.exp u)*u*Real.exp (-gain v u c) := by
  obtain ⟨C, hC, h⟩ := eventual_coprime_avoid_count_bound
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  have ht : Tendsto (fun v : ℝ => Real.exp (Real.exp ((4/5)*v))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4/5)))
  refine ⟨C*(1+Real.exp (Real.log 4+1)), by positivity, ?_⟩
  filter_upwards [eventual_window_conditions c hc, eventual_source_mass_bounds c hc,
    eventual_scale_bounds c hc, ht.eventually_ge_atTop X, eventually_ge_atTop (2 : ℝ)]
    with v hv hm hscale hvX hv2 u hulo hule m
  have hv0 : 0 < v := by linarith
  have hw : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hu : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hg : gain v u c ≤ u := by unfold gain; linarith
  have hg0 := (hscale u hulo hule).2.1
  obtain ⟨hp, hq⟩ := hv u hulo hule
  obtain ⟨hpm, hqm⟩ := hm u hulo hule
  have hxx : X ≤ Real.exp (Real.exp u) := hvX.trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))
  have hcut : HarperRoundedCutoff.smoothCutoff (Real.exp (Real.exp u)) =
      Real.exp (Real.exp u/u) := by
    rw [KorolevSmoothCount.smoothCutoff_eq_exp (Real.exp_pos _), Real.log_exp, Real.log_exp]
  have hps : pPrimes v u c ⊆ CollisionMertensInput.primesUpTo
      (HarperRoundedCutoff.smoothCutoff (Real.exp (Real.exp u))) := by
    rw [hcut]
    exact selected_subset (Real.exp_pos v).le hp.first_pos hp.cutoff
  have hqs : qPrimes v u c ⊆ CollisionMertensInput.primesUpTo
      (HarperRoundedCutoff.smoothCutoff (Real.exp (Real.exp u))) := by
    rw [hcut]
    intro p hpp
    obtain ⟨hprime, _, hhigh⟩ := KorolevPrimeIntervals.intervalPrimes_mem.mp hpp
    exact CollisionMertensInput.primesUpTo_mem.mpr ⟨hprime, hhigh.trans hq.cutoff⟩
  have hpc := hX _ hxx _ hps m
  have hqc := hX _ hxx _ hqs m
  simp only [Real.log_exp] at hpc hqc
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨absorb_count hC.le (Real.exp_pos _).le hu hg _ _ ?_ hpc,
    absorb_count hC.le (Real.exp_pos _).le hu hg _ _ ?_ hqc⟩
  · change gain v u c-Real.log 4/2-1 ≤ ∑ p ∈ pPrimes v u c, (1 : ℝ)/p at hpm
    linarith
  · change 2*gain v u c-Real.log 4-1 ≤ ∑ p ∈ qPrimes v u c, (1 : ℝ)/p at hqm
    linarith

end NField.Alignment.KorolevParameterCount
