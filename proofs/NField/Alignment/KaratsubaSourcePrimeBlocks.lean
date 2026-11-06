/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaPrimeBlockMoment
import NField.Alignment.KorolevCoarseBlockPopulation
import NField.Alignment.KorolevUncutPrimeRectangle

/-! # Uniform cancellation on actual logarithmic source-prime blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourcePrimeBlocks
open Filter KorolevPrimeWindows KorolevPrimeIntervals KorolevLogarithmicPartition
  KorolevWindowParameters KorolevSourceWindowDensity KaratsubaSourceWindows
open scoped Topology

def coprimeBlock (m : ℕ) (l D A : ℝ) (i : ℕ) : Finset ℕ :=
  (block l D A i).filter (fun p => p.Coprime m)

/-- A coprime block belongs to its original interval, not to a changed ambient canonical family. -/
theorem coprimeBlock_subset {m : ℕ} {l D A : ℝ} (hA : 0 < A) (hD : A ≤ D)
    {i : ℕ} (hi : i < blockCount D A) :
    coprimeBlock m l D A i ⊆
      (intervalPrimes (Real.exp l) (Real.exp (l+D))).filter (fun p => p.Coprime m) := by
  intro p hp
  obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hp
  have hh := Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hb⟩
  rw [biUnion_blocks l hA hD] at hh
  exact Finset.mem_filter.mpr ⟨hh, hc⟩

/-- The source upper endpoint never has logarithm larger than the modulus coordinate. -/
theorem log_upper_le {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (upperEndpoint L k) ≤ L := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [log_upper]
  have hh := div_le_self hL (show 1 ≤ 2*(k : ℝ)-1 by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-- The full source range provides exponential power saving normalized by actual block populations. -/
theorem eventual_source_block_power_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      ∀ lp lq Dp Dq : ℝ, 1 ≤ lp → 1 ≤ lq → A ≤ Dp → A ≤ Dq →
      Real.exp lp = lowerEndpoint (Real.log m) k →
      Real.exp lq = upperEndpoint (Real.log m) (s+1) →
      Real.exp (lp+Dp) = upperEndpoint (Real.log m) k →
      Real.exp (lq+Dq) = upperEndpoint (Real.log m) s →
      ∀ i j : ℕ, i < blockCount Dp A → j < blockCount Dq A →
      ∀ P₀ Q₀ : Finset ℕ, P₀ ⊆ coprimeBlock m lp Dp A i → Q₀ ⊆ coprimeBlock m lq Dq A j →
      ∀ a b : ZMod m,
      (‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
        (((coprimeBlock m lp Dp A i).card : ℝ)*((coprimeBlock m lq Dq A j).card : ℝ)))^(2*s*k) ≤
          (a.val.gcd m : ℝ)*Real.exp (-Real.log m/(128*(k : ℝ)^2)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc : 0 ≤ Real.log C := Real.log_nonneg hC
  filter_upwards [ht.eventually KaratsubaPrimeBlockMoment.eventual_envelope_subset_bound,
    KorolevCoarseBlockPopulation.eventual_coarse_population_nat C hC A hA herror,
    ht.eventually (eventual_index_envelope (Real.log C) hc),
    ht.eventually (KorolevIndexSeparation.eventual_selected_index_separation (Real.log C) hc),
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) hc),
    hlog.eventually_gt_atTop 1]
    with m hb hp he hsep hfirst hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
      lp lq Dp Dq hlp hlq hDp hDq hLp hLq hUp hUq i j hi hj P₀ Q₀ hPsub hQsub a b
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hf := hfirst (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hf
  have hk : 1 ≤ k := by omega
  have hs : 1 ≤ s := by omega
  have hA0 : 0 < A := by linarith
  have hsep' := hsep (Real.log (Real.log x)) hulo hule k s hklast hsfirst
  have hei := he (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hei
  have hse : (s : ℝ) ≤ KorolevSourceEnvelope.envelope (Real.log (Real.log m)) := by
    have hh : (s : ℝ) ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) := by exact_mod_cast hslast
    linarith [hei.2]
  have hcoord : Real.log (m : ℝ) = Real.exp (Real.log (Real.log m)) :=
    (Real.exp_log (by linarith : 0 < Real.log (m : ℝ))).symm
  have hPEnd : lp+Dp ≤ Real.log (m : ℝ) := by
    have hh : lp+Dp = Real.log (upperEndpoint (Real.log m) k) := by rw [← hUp, Real.log_exp]
    rw [hh]
    exact log_upper_le (by linarith) hk
  have hQEnd : lq+Dq ≤ Real.log (m : ℝ) := by
    have hh : lq+Dq = Real.log (upperEndpoint (Real.log m) s) := by rw [← hUq, Real.log_exp]
    rw [hh]
    exact log_upper_le (by linarith) hs
  have hPbase : upperEndpoint (Real.log m) (k+1) ≤ Real.exp lp := by
    rw [hLp]
    exact (successor_separation (by linarith) hk).le
  have hQbase : upperEndpoint (Real.log m) (s+1) ≤ Real.exp lq := by rw [hLq]
  have hpPop := hp x hlo hhi k hk (Or.inl hklast) lp Dp hlp hPbase hDp hPEnd i hi
  have hqPop := hp x hlo hhi s hs (Or.inr hslast) lq Dq hlq hQbase hDq hQEnd j hj
  rw [hLp] at hpPop
  rw [hLq] at hqPop
  have hPSrc : coprimeBlock m lp Dp A i ⊆ pPrimes m k := by
    have hh := coprimeBlock_subset (m := m) (l := lp) hA0 hDp hi
    rw [hLp, hUp] at hh
    exact hh
  have hQSrc : coprimeBlock m lq Dq A j ⊆ qPrimes m s := by
    have hh := coprimeBlock_subset (m := m) (l := lq) hA0 hDq hj
    rw [hLq, hUq] at hh
    exact hh
  exact hb m hcoord k s hk hs hse hsep' P₀ Q₀ (coprimeBlock m lp Dp A i)
    (coprimeBlock m lq Dq A j) hPsub hQsub hPSrc hQSrc hpPop hqPop a b

end NField.Alignment.KaratsubaSourcePrimeBlocks
