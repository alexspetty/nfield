/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSquarefreeRepresentation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Asymptotic form of Korolev's squarefree representation lemma

The actual union of three exception sets has O(x log(log x)/(log x)^gamma)
cardinality in the original source range. Outside it, the literal
n=l^2*p*q*h representation has both interval indices and nonzero Mobius
value. The absolute constant is proved to exist; the printed constant
60 is not certified. The bilinear and final Korolev inputs remain open.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevLemmaA
open Filter KorolevSourceScales KorolevWindowParameters KorolevPrimeWindows
  KorolevParameterCount KorolevSourceWindowCount KorolevPrimeSeparation
  KorolevSquarefreeRepresentation KorolevLargeSquares KorolevMissingPrimeCount
open scoped Topology Classical ArithmeticFunction.Moebius

def SourceRepresentation (C m x : ℝ) (n : ℕ) : Prop :=
  ∃ l p q h k s : ℕ,
    1 ≤ l ∧ (l : ℝ) ≤ Real.log x ∧ 0 < h ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧
    pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k ∧
    k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ∧
    qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s ∧
    s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ∧
    lowerEndpoint (Real.log m) k < (p : ℝ) ∧ (p : ℝ) ≤ upperEndpoint (Real.log m) k ∧
    upperEndpoint (Real.log m) (s+1) < (q : ℝ) ∧ (q : ℝ) ≤ upperEndpoint (Real.log m) s ∧
    μ (p*q*h) ≠ 0 ∧ n = l^2*p*q*h

theorem source_representation_of_selected {C m x : ℝ} (hL : 0 < Real.log m)
    (hqa : 1 ≤ qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
    (hqab : qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤
      qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
    {n : ℕ} (hn : HasSelectedRepresentation x (sourcePPrimes C m x) (sourceQPrimes C m x) n) :
    SourceRepresentation C m x n := by
  obtain ⟨l, p, q, h, hl, hlx, hh, hpp, hqp, hpq, hp, hq, hform, hsf⟩ := hn
  have hp' : p ∈ selectedPrimes (Real.log m)
      (pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
      (pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)) := by
    simpa only [sourcePPrimes, pPrimes, Real.exp_log hL] using hp
  have hq' : q ∈ KorolevPrimeIntervals.intervalPrimes
      (upperEndpoint (Real.log m) (qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)+1))
      (upperEndpoint (Real.log m) (qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))) := by
    simpa only [sourceQPrimes, qPrimes, Real.exp_log hL] using hq
  obtain ⟨k, hk1, hk2, _, hpk1, hpk2⟩ := (selectedPrimes_mem _ _ _ _).mp hp'
  obtain ⟨s, hs1, hs2, _, hqs1, hqs2⟩ := (contiguous_interval_membership hL.le hqa hqab).mp hq'
  exact ⟨l, p, q, h, k, s, hl, hlx, hh, hpp, hqp, hpq, hk1, hk2, hs1, hs2,
    hpk1, hpk2, hqs1, hqs2, ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf, hform⟩

theorem eventual_source_representation (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        (((exceptionSet x (sourcePPrimes C m x) (sourceQPrimes C m x)).filter
          (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) ∧
        ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x → n.Coprime modulus →
          n ∉ exceptionSet x (sourcePPrimes C m x) (sourceQPrimes C m x) →
          SourceRepresentation C m x n := by
  obtain ⟨K, hK, hcounts⟩ := eventual_source_window_counts C hC
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine ⟨2+2*K, by positivity, ?_⟩
  filter_upwards [hcounts, eventual_source_prime_properties C hC,
    ht.eventually (eventual_window_conditions (Real.log C) (Real.log_nonneg hC)),
    eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1,
    ht.eventually_ge_atTop 2] with m hm hp hw hm0 hL hv2 x hlo hhi modulus
  dsimp only [Function.comp_apply] at hw hv2
  obtain ⟨hx, hY, hulo, hule⟩ := source_log_range hm0 hL hlo hhi
  have hlogv : 0 ≤ Real.log (Real.log (Real.log m)) := Real.log_nonneg (by linarith)
  have hu : 1 ≤ Real.log (Real.log x) := by linarith
  have hu0 : 0 < Real.log (Real.log x) := by linarith
  have hgain : gain (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤
      Real.log (Real.log x) := by
    have hc := Real.log_nonneg hC
    unfold gain
    linarith
  have hdec : 1/Real.log x ≤ (Real.log x)^(-sourceGamma C m x) := by
    rw [← source_decay_identity hY hu0.ne']
    calc
      _ = Real.exp (-Real.log (Real.log x)) := by rw [Real.exp_neg, Real.exp_log hY, one_div]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hscale : x/Real.log x ≤ x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) := by
    calc
      _ = x*(1/Real.log x) := by ring
      _ ≤ _ := mul_le_mul (by nlinarith : x ≤ x*Real.log (Real.log x)) hdec
        (by positivity) (by positivity)
  have hsquare := coprime_large_square_count hx.le hY modulus
  have hsmall : (((largeSquareSet x (Real.log x)).filter (fun n => n.Coprime modulus)).card : ℝ) ≤
      2*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) := by
    apply hsquare.trans
    calc
      2*x/Real.log x = 2*(x/Real.log x) := by ring
      _ ≤ 2*(x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x)) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = _ := by ring
  obtain ⟨hpc, hqc⟩ := hm x hlo hhi modulus
  constructor
  · have he := exception_count_le x (sourcePPrimes C m x) (sourceQPrimes C m x) modulus
    nlinarith
  · intro n hn hnx _hcop hout
    have hr := representation_outside_exception hx.le (hp x hlo hhi) hn hnx hout
    have hq := (hw _ hulo hule).2
    exact source_representation_of_selected (by linarith) hq.first_pos hq.ordered hr


def failureSet (C m x : ℝ) (modulus : ℕ) : Finset ℕ :=
  (HarperIntervalSieve.intervalSupport 0 x).filter
    (fun n => n.Coprime modulus ∧ ¬SourceRepresentation C m x n)

theorem eventual_actual_failure_count (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        ((failureSet C m x modulus).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) := by
  obtain ⟨K, hK, h⟩ := eventual_source_representation C hC
  refine ⟨K, hK, ?_⟩
  filter_upwards [h] with m hm x hlo hhi modulus
  obtain ⟨hcount, hrep⟩ := hm x hlo hhi modulus
  have hx : 0 ≤ x := (Real.exp_pos _).le.trans hlo
  have hsub : failureSet C m x modulus ⊆
      (exceptionSet x (sourcePPrimes C m x) (sourceQPrimes C m x)).filter
        (fun n => n.Coprime modulus) := by
    intro n hn
    obtain ⟨hnrange, hcop, hfail⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnx⟩ := (HarperIntervalSieve.intervalSupport_mem (by norm_num) hx n).mp hnrange
    have hnpos : 0 < n := by exact_mod_cast hn0
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcop⟩
    by_contra hout
    exact hfail (hrep n hnpos hnx hcop hout)
  exact (by exact_mod_cast Finset.card_le_card hsub :
    ((failureSet C m x modulus).card : ℝ) ≤
      (((exceptionSet x (sourcePPrimes C m x) (sourceQPrimes C m x)).filter
        (fun n => n.Coprime modulus)).card : ℝ)).trans hcount

end NField.Alignment.KorolevLemmaA
