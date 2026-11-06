/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourcePrimeBlockNorm

/-! # Correlated source indices and uniform ordinary block decay

The two selected scales must be estimated together. Their correlation
retains a cubic logarithmic saving even after the upper-index rounding.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceIndexDecay
open Filter KorolevSourceScales KorolevWindowParameters KorolevEndpointIndices
open KorolevPrimeWindows KorolevLogarithmicPartition KaratsubaSourcePrimeBlocks
open scoped Topology

/-- The exact correlated product of the two upper source scales. -/
theorem stop_product (v u c : ℝ) :
    2*(pStop v u c)^3*qStop v u c =
      Real.exp ((16*v-5*u-11*Real.log v-11*c)/12)/2 := by
  unfold pStop qStop
  rw [div_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (16*v-5*u-11*Real.log v-11*c)/12 =
      3*(v-u+4*gain v u c)+(2*v-2*u+10*gain v u c) := by
    unfold gain
    ring
  conv_rhs => rw [he, Real.exp_add]
  ring

/-- The original lower source range makes the correlated product small. -/
theorem stop_product_bound {v u c : ℝ} (hv : 0 < v) (hc : 0 ≤ c)
    (hulo : (4/5)*v+5*Real.log v ≤ u) :
    2*(pStop v u c)^3*qStop v u c ≤ Real.exp v/(2*v^3) := by
  rw [stop_product]
  have he : (16*v-5*u-11*Real.log v-11*c)/12 ≤ v-3*Real.log v := by
    linarith
  have hb := Real.exp_le_exp.mpr he
  have hid : Real.exp (v-3*Real.log v) = Real.exp v/v^3 := by
    rw [Real.exp_sub, show (3 : ℝ)*Real.log v = (3 : ℕ)*Real.log v by norm_num,
      Real.exp_nat_mul, Real.exp_log hv]
  rw [hid] at hb
  calc
    _ ≤ (Real.exp v/v^3)/2 := div_le_div_of_nonneg_right hb (by norm_num)
    _ = _ := by ring

/-- Actual upper indices retain the correlated saving, including their offsets. -/
theorem rounded_index_product {v u c : ℝ} (hv : 0 < v) (hc : 0 ≤ c)
    (hulo : (4/5)*v+5*Real.log v ≤ u)
    (hp : 2 ≤ pStop v u c) (hq : 2 ≤ qStop v u c)
    {k s : ℕ} (hk : k ≤ pLast v u c) (hs : s ≤ qLast v u c) :
    (k : ℝ)^3*(s : ℝ) ≤ Real.exp v/(2*v^3) := by
  have hpB := (upperIndex_bounds hp (by norm_num : (1 : ℕ) ≤ 1)).2
  have hqB := (upperIndex_bounds hq (by norm_num : (0 : ℕ) ≤ 1)).2
  norm_num only [Nat.cast_one, Nat.cast_zero] at hpB hqB
  have hkR : (k : ℝ) ≤ pLast v u c := by exact_mod_cast hk
  have hsR : (s : ℝ) ≤ qLast v u c := by exact_mod_cast hs
  change (pLast v u c : ℝ) ≤ pStop v u c-(1 : ℝ)+1/2 at hpB
  change (qLast v u c : ℝ) ≤ qStop v u c-(0 : ℝ)+1/2 at hqB
  have hkP : (k : ℝ) ≤ pStop v u c := by linarith
  have hsQ : (s : ℝ) ≤ 2*qStop v u c := by linarith
  have hkp := pow_le_pow_left₀ (Nat.cast_nonneg k) hkP 3
  calc
    _ ≤ (pStop v u c)^3*(2*qStop v u c) :=
      mul_le_mul hkp hsQ (Nat.cast_nonneg s) (by positivity)
    _ = 2*(pStop v u c)^3*qStop v u c := by ring
    _ ≤ _ := stop_product_bound hv hc hulo

/-- Both original source ranges and actual rounded upper indices are uniform. -/
theorem eventual_index_product (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ k s : ℕ,
      k ≤ pLast v u c → s ≤ qLast v u c →
      (k : ℝ)^3*(s : ℝ) ≤ Real.exp v/(2*v^3) := by
  filter_upwards [eventual_scale_bounds c hc, eventually_gt_atTop (0 : ℝ)]
    with v he hv u hulo hule k s hk hs
  obtain ⟨_, hg, hp, hq, h4, _, _, _⟩ := he u hulo hule
  have hpStop : 2 ≤ pStop v u c := by
    rw [pStop_ratio]
    nlinarith
  have hqStop : 2 ≤ qStop v u c := by
    rw [qStop_ratio]
    nlinarith
  exact rounded_index_product hv hc hulo hpStop hqStop hk hs

/-- The moment-root exponential saving is at least cubic in log log m. -/
theorem decay_of_index_product {v : ℝ} {k s : ℕ} (hv : 0 < v)
    (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hprod : (k : ℝ)^3*(s : ℝ) ≤ Real.exp v/(2*v^3)) :
    Real.exp (-Real.exp v/(256*(s : ℝ)*(k : ℝ)^3)) ≤
      Real.exp (-v^3/128) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hh := (le_div_iff₀ (show 0 < 2*v^3 by positivity)).mp hprod
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  apply neg_le_neg
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 128)
    (show 0 < 256*(s : ℝ)*(k : ℝ)^3 by positivity)).mpr
  nlinarith [hh]

/-- The original source range gives uniform decay at every selected index pair. -/
theorem eventual_source_decay (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      Real.exp (-Real.log m/(256*(s : ℝ)*(k : ℝ)^3)) ≤
        Real.exp (-(Real.log (Real.log m))^3/128) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc := Real.log_nonneg hC
  filter_upwards [ht.eventually (eventual_index_product (Real.log C) hc),
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) hc),
    ht.eventually_gt_atTop 0, hlog.eventually_gt_atTop 1]
    with m hp hf hv hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hh := hf (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hh hp hv
  have hk : 1 ≤ k := by omega
  have hs : 1 ≤ s := by omega
  have hprod := hp (Real.log (Real.log x)) hulo hule k s hklast hslast
  have hd := decay_of_index_product hv hk hs hprod
  rw [Real.exp_log (by linarith : 0 < Real.log (m : ℝ))] at hd
  exact hd

/-- Uniform cubic logarithmic decay for the actual source blocks and all their subsets. -/
theorem eventual_uniform_source_block_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
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
      ‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
        (((coprimeBlock m lp Dp A i).card : ℝ)*((coprimeBlock m lq Dq A j).card : ℝ)) ≤
          (a.val.gcd m : ℝ)^(((2*s*k : ℕ) : ℝ)⁻¹)*
            Real.exp (-(Real.log (Real.log m))^3/128) := by
  filter_upwards [KaratsubaSourcePrimeBlockNorm.eventual_source_block_bound C hC A hA herror,
    eventual_source_decay C hC]
    with m hb hd inst x hlo hhi k s hkfirst hklast hsfirst hslast
      lp lq Dp Dq hlp hlq hDp hDq hLp hLq hUp hUq i j hi hj P₀ Q₀ hPsub hQsub a b
  exact (hb x hlo hhi k s hkfirst hklast hsfirst hslast lp lq Dp Dq hlp hlq hDp hDq
    hLp hLq hUp hUq i j hi hj P₀ Q₀ hPsub hQsub a b).trans
    (mul_le_mul_of_nonneg_left (hd x hlo hhi k s hkfirst hklast hsfirst hslast)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end NField.Alignment.KorolevSourceIndexDecay
