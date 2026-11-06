/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevActualPrimeBlocks

/-! # Polynomial population bounds for the actual source logarithmic blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevActualBlockCount
open Filter KorolevPrimeWindows KorolevWindowParameters KorolevActualPrimeBlocks
  KorolevLogarithmicPartition KorolevSourceEnvelope KaratsubaSourcePrimeBlocks
open scoped Topology BigOperators

/-- With fixed width at least one, the number of blocks is at most the interval's log width. -/
theorem count_le_width {A D : ℝ} (hA : 1 ≤ A) (hD : A ≤ D) :
    (blockCount D A : ℝ) ≤ D := by
  exact (count_width (by linarith : 0 < A) hD).2.2.2.trans
    (div_le_self (by linarith : 0 ≤ D) hA)

/-- Uniform width bounds and the actual endpoint-index population control the full block count. -/
theorem sum_count_le_sq {a b : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hb : (b : ℝ)+1 ≤ L) (n : ℕ → ℕ)
    (hn : ∀ k ∈ Finset.Icc a b, (n k : ℝ) ≤ L) :
    (∑ k ∈ Finset.Icc a b, (n k : ℝ)) ≤ L^2 := by
  have hcard : ((Finset.Icc a b).card : ℝ) ≤ L := by
    have hh : (Finset.Icc a b).card ≤ b+1 := by simp only [Nat.card_Icc]; omega
    exact (show ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ)+1 by exact_mod_cast hh).trans hb
  calc
    _ ≤ ∑ _k ∈ Finset.Icc a b, L := Finset.sum_le_sum hn
    _ = ((Finset.Icc a b).card : ℝ)*L := by simp
    _ ≤ L*L := mul_le_mul_of_nonneg_right hcard hL
    _ = _ := by ring

/-- The common source-index envelope is eventually below the modulus logarithm. -/
theorem eventual_envelope_le_exp : ∀ᶠ v : ℝ in atTop, envelope v ≤ Real.exp v := by
  filter_upwards [eventual_envelope_small 1, eventually_ge_atTop (0 : ℝ)] with v hs hv
  have he : 1 ≤ Real.exp (5*v/12) := Real.one_le_exp (by positivity)
  have henv : 1 ≤ envelope v := by unfold envelope; linarith
  have hsq := (div_le_iff₀ (Real.exp_pos v)).mp hs
  nlinarith

/-- Both actual source families have at most exp(v)^2 logarithmic blocks. -/
theorem eventual_counts (c : ℝ) (hc : 0 ≤ c) (A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ v : ℝ in atTop, ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      (∑ k ∈ Finset.Icc (pFirst v u c) (pLast v u c),
        (blockCount (pWidth (Real.exp v) k) A : ℝ)) ≤ (Real.exp v)^2 ∧
      (∑ s ∈ Finset.Icc (qFirst v u c) (qLast v u c),
        (blockCount (qWidth (Real.exp v) s) A : ℝ)) ≤ (Real.exp v)^2 := by
  filter_upwards [eventual_parameters c hc A (by linarith),
    KorolevSourceWindowDensity.eventual_index_envelope c hc,
    KorolevUncutPrimeRectangle.eventual_first_indices_ge_two c hc,
    eventual_envelope_le_exp] with v hp hi hf he u hulo hule
  have hparams := hp u hulo hule
  have hindices := hi u hulo hule
  have hfirst := hf u hulo hule
  constructor
  · apply sum_count_le_sq (Real.exp_pos v).le (hindices.1.trans he)
    intro k hk
    obtain ⟨hkfirst, hklast⟩ := Finset.mem_Icc.mp hk
    have hkpos : 1 ≤ k := by omega
    have hh := hparams k hkpos (Or.inl hklast)
    apply (count_le_width hA hh.2.2.1).trans
    have hu := log_upper_le (Real.exp_pos v).le hkpos
    unfold pWidth
    linarith [hh.1]
  · apply sum_count_le_sq (Real.exp_pos v).le (hindices.2.trans he)
    intro s hs
    obtain ⟨hsfirst, hslast⟩ := Finset.mem_Icc.mp hs
    have hspos : 1 ≤ s := by omega
    have hh := hparams s hspos (Or.inr hslast)
    apply (count_le_width hA hh.2.2.2).trans
    have hu := log_upper_le (Real.exp_pos v).le hspos
    unfold qWidth
    linarith [hh.2.1]

/-- Polynomial block populations throughout the original integer-modulus source range. -/
theorem eventual_source_counts (C : ℝ) (hC : 1 ≤ C) (A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) →
      (∑ k ∈ Finset.Icc
        (pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
        (pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)),
        (blockCount (pWidth (Real.log m) k) A : ℝ)) ≤ (Real.log m)^2 ∧
      (∑ s ∈ Finset.Icc
        (qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
        (qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)),
        (blockCount (qWidth (Real.log m) s) A : ℝ)) ≤ (Real.log m)^2 := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [ht.eventually (eventual_counts (Real.log C) (Real.log_nonneg hC) A hA),
    hlog.eventually_gt_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with m hb hL hm x hlo hhi
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hh := hb (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hh
  simpa only [Real.exp_log (by linarith : 0 < Real.log (m : ℝ))] using hh

end NField.Alignment.KorolevActualBlockCount
