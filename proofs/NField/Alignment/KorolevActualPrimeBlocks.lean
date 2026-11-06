/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourceIndexDecay
import NField.Alignment.KorolevSourceLogarithmicPartition

/-! # Literal logarithmic partitions of the selected source intervals

The source endpoints determine the partition data; their validity is
discharged uniformly rather than supplied as an analytic hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevActualPrimeBlocks
open Filter KorolevPrimeWindows KorolevWindowParameters KorolevSourceScales
  KorolevLogarithmicPartition KorolevSourceEnvelope KaratsubaSourcePrimeBlocks
open scoped Topology

def pLog (L : ℝ) (k : ℕ) : ℝ := Real.log (lowerEndpoint L k)
def pWidth (L : ℝ) (k : ℕ) : ℝ := Real.log (upperEndpoint L k)-pLog L k
def qLog (L : ℝ) (s : ℕ) : ℝ := Real.log (upperEndpoint L (s+1))
def qWidth (L : ℝ) (s : ℕ) : ℝ := Real.log (upperEndpoint L s)-qLog L s

/-- Both endpoints of the P partition are exactly the source endpoints. -/
theorem p_endpoints (L : ℝ) (k : ℕ) :
    Real.exp (pLog L k) = lowerEndpoint L k ∧
    Real.exp (pLog L k+pWidth L k) = upperEndpoint L k := by
  constructor
  · exact Real.exp_log (lowerEndpoint_pos L k)
  · simp only [pWidth, add_sub_cancel]
    exact Real.exp_log (upperEndpoint_pos L k)

/-- Both endpoints of the Q partition are exactly the consecutive source endpoints. -/
theorem q_endpoints (L : ℝ) (s : ℕ) :
    Real.exp (qLog L s) = upperEndpoint L (s+1) ∧
    Real.exp (qLog L s+qWidth L s) = upperEndpoint L s := by
  constructor
  · exact Real.exp_log (upperEndpoint_pos L (s+1))
  · simp only [qWidth, add_sub_cancel]
    exact Real.exp_log (upperEndpoint_pos L s)

/-- The exact partition data satisfy every positivity and width condition in the source range. -/
theorem eventual_parameters (c : ℝ) (hc : 0 ≤ c) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ v : ℝ in atTop, ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      ∀ k : ℕ, 1 ≤ k → (k ≤ pLast v u c ∨ k ≤ qLast v u c) →
        1 ≤ pLog (Real.exp v) k ∧ 1 ≤ qLog (Real.exp v) k ∧
          A ≤ pWidth (Real.exp v) k ∧ A ≤ qWidth (Real.exp v) k := by
  filter_upwards [KorolevSourceWindowDensity.eventual_index_envelope c hc,
    KorolevSourceLogarithmicPartition.eventual_envelope_width A hA,
    eventual_envelope_small (3*(1+Real.log 4))]
    with v he hw hsmall u hulo hule k hk hlast
  have hi := he u hulo hule
  have hkenv : (k : ℝ) ≤ envelope v := by
    rcases hlast with hp | hq
    · have hh : (k : ℝ) ≤ pLast v u c := by exact_mod_cast hp
      linarith [hi.1]
    · have hh : (k : ℝ) ≤ qLast v u c := by exact_mod_cast hq
      linarith [hi.2]
  have hwidth := hw k hk hkenv
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg k) hkenv 2
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsize : (1+Real.log 4)*(2*(k : ℝ)+1) ≤ Real.exp v := by
    have hb := (div_le_iff₀ (Real.exp_pos v)).mp hsmall
    have hpoly : 2*(k : ℝ)+1 ≤ 3*(k : ℝ)^2 := by
      nlinarith [sq_nonneg ((k : ℝ)-1)]
    calc
      _ ≤ (1+Real.log 4)*(3*(k : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hpoly (by linarith)
      _ ≤ 3*(1+Real.log 4)*(envelope v)^2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsquare
          (show 0 ≤ 3*(1+Real.log 4) by positivity)]
      _ ≤ Real.exp v := by simpa only [one_mul] using hb
  have hq : 1 ≤ qLog (Real.exp v) k :=
    KorolevFixedRatioSourceBlocks.contiguous_log_ge hsize
  have hsep := Real.log_le_log (upperEndpoint_pos (Real.exp v) (k+1))
    (successor_separation (Real.exp_pos v).le hk).le
  exact ⟨hq.trans hsep, hq, hwidth.1, hwidth.2⟩

/-- The block norm bound on the literal source partition, with no partition-validity hypotheses. -/
theorem eventual_actual_source_block_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      ∀ i j : ℕ, i < blockCount (pWidth (Real.log m) k) A → j < blockCount (qWidth (Real.log m) s) A →
      ∀ P₀ Q₀ : Finset ℕ, P₀ ⊆ coprimeBlock m (pLog (Real.log m) k) (pWidth (Real.log m) k) A i → Q₀ ⊆ coprimeBlock m (qLog (Real.log m) s) (qWidth (Real.log m) s) A j →
      ∀ a b : ZMod m,
      ‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
        (((coprimeBlock m (pLog (Real.log m) k) (pWidth (Real.log m) k) A i).card : ℝ)*((coprimeBlock m (qLog (Real.log m) s) (qWidth (Real.log m) s) A j).card : ℝ)) ≤
          (a.val.gcd m : ℝ)^(((2*s*k : ℕ) : ℝ)⁻¹)*
            Real.exp (-(Real.log (Real.log m))^3/128) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc := Real.log_nonneg hC
  filter_upwards [KorolevSourceIndexDecay.eventual_uniform_source_block_bound C hC A hA herror,
    ht.eventually (eventual_parameters (Real.log C) hc A (by linarith)),
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) hc),
    hlog.eventually_gt_atTop 1]
    with m hb hp hf hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
      i j hi hj P₀ Q₀ hPsub hQsub a b
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hh := hf (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hh hp
  have hk : 1 ≤ k := by omega
  have hs : 1 ≤ s := by omega
  have hkP := hp (Real.log (Real.log x)) hulo hule k hk (Or.inl hklast)
  have hsQ := hp (Real.log (Real.log x)) hulo hule s hs (Or.inr hslast)
  have hcoord : Real.exp (Real.log (Real.log m)) = Real.log m :=
    Real.exp_log (by linarith : 0 < Real.log (m : ℝ))
  rw [hcoord] at hkP hsQ
  exact hb x hlo hhi k s hkfirst hklast hsfirst hslast
    (pLog (Real.log m) k) (qLog (Real.log m) s)
    (pWidth (Real.log m) k) (qWidth (Real.log m) s)
    hkP.1 hsQ.2.1 hkP.2.2.1 hsQ.2.2.2
    (p_endpoints _ _).1 (q_endpoints _ _).1 (p_endpoints _ _).2 (q_endpoints _ _).2
    i j hi hj P₀ Q₀ hPsub hQsub a b

end NField.Alignment.KorolevActualPrimeBlocks
