/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevBlockSawtoothBound
import NField.Alignment.KorolevBlockResidualVolume

/-! # Canonical sawtooth estimates on the literal source-prime blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevActualSawtoothBlocks
open Filter KorolevPrimeWindows KorolevWindowParameters KorolevActualPrimeBlocks
  KorolevLogarithmicPartition KaratsubaSourcePrimeBlocks KorolevCanonicalPrimeSlices
  KorolevCanonicalPhaseSlices KorolevBlockSawtoothBound
  DedekindReciprocity DedekindInverseResidueTransform
open scoped Topology BigOperators Classical

/-- A raw P block belongs to the original separated source window. -/
theorem p_block_subset (L : ℝ) (k : ℕ) {A : ℝ} (hA : 0 < A)
    (hD : A ≤ pWidth L k) {i : ℕ} (hi : i < blockCount (pWidth L k) A) :
    block (pLog L k) (pWidth L k) A i ⊆ windowPrimes L k := by
  intro p hp
  have hh := Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hp⟩
  rw [biUnion_blocks (pLog L k) hA hD, (p_endpoints L k).1,
    (p_endpoints L k).2] at hh
  exact hh

/-- A raw Q block belongs to its original contiguous source step. -/
theorem q_block_subset (L : ℝ) (s : ℕ) {A : ℝ} (hA : 0 < A)
    (hD : A ≤ qWidth L s) {j : ℕ} (hj : j < blockCount (qWidth L s) A) :
    block (qLog L s) (qWidth L s) A j ⊆
      KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s) := by
  intro q hq
  have hh := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hq⟩
  rw [biUnion_blocks (qLog L s) hA hD, (q_endpoints L s).1,
    (q_endpoints L s).2] at hh
  exact hh

/-- The actual canonical sawtooth slice has uniform cubic log-log decay. -/
theorem eventual_sawtooth_block_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      ∀ i j : ℕ, i < blockCount (pWidth (Real.log m) k) A →
      j < blockCount (qWidth (Real.log m) s) A →
      ∀ P Q : Finset ℕ, ∀ l h X r : ℕ,
      0 < l → 0 < h → l.Coprime m → h.Coprime m → r.Coprime m →
      ‖primeSliceOn P Q
        (block (pLog (Real.log m) k) (pWidth (Real.log m) k) A i)
        (block (qLog (Real.log m) s) (qWidth (Real.log m) s) A j) l h X m
        (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))‖ ≤
        K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
          Real.exp (-(Real.log (Real.log m))^3/128)*
          ((coprimeBlock m (pLog (Real.log m) k) (pWidth (Real.log m) k) A i).card : ℝ)*
          ((coprimeBlock m (qLog (Real.log m) s) (qWidth (Real.log m) s) A j).card : ℝ) := by
  obtain ⟨K, hK, hf⟩ := KorolevSourceFrequencyWeight.eventual_source_frequency_bound C hC
  refine ⟨K, hK, ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc := Real.log_nonneg hC
  filter_upwards [eventual_actual_source_block_bound C hC A hA herror, hf,
    KorolevUncutPrimeRectangle.eventual_source_rectangle C hC,
    ht.eventually (eventual_parameters (Real.log C) hc A (by linarith)),
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) hc),
    hlog.eventually_gt_atTop 1]
    with m hb hfreq hrange hp hfirst hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
      i j hi hj P Q l h X r hlpos hhpos hl hh hr
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hhfirst := hfirst (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hhfirst hp
  have hk : 1 ≤ k := by omega
  have hs : 1 ≤ s := by omega
  have hkP := hp (Real.log (Real.log x)) hulo hule k hk (Or.inl hklast)
  have hsQ := hp (Real.log (Real.log x)) hulo hule s hs (Or.inr hslast)
  have hcoord : Real.exp (Real.log (Real.log m)) = Real.log m :=
    Real.exp_log (by linarith : 0 < Real.log (m : ℝ))
  rw [hcoord] at hkP hsQ
  have hA0 : 0 < A := by linarith
  have hrect : ∀ p ∈ block (pLog (Real.log m) k) (pWidth (Real.log m) k) A i,
      ∀ q ∈ block (qLog (Real.log m) s) (qWidth (Real.log m) s) A j, p*q < m := by
    intro p hp' q hq'
    exact hrange x hlo hhi k s hkfirst hsfirst p
      (p_block_subset _ _ hA0 hkP.2.2.1 hi hp') q
      (q_block_subset _ _ hA0 hsQ.2.2.2 hj hq')
  have hbil (a b : ZMod m) := absolute_of_normalized
    (canonicalDomain_subset P h m (pLog (Real.log m) k) (pWidth (Real.log m) k) A i)
    (canonicalDomain_subset Q h m (qLog (Real.log m) s) (qWidth (Real.log m) s) A j) a b
    (hb x hlo hhi k s hkfirst hklast hsfirst hslast i j hi hj _ _
      (canonicalDomain_subset P h m _ _ _ _)
      (canonicalDomain_subset Q h m _ _ _ _) a b)
  have hmain := norm_sawtooth_of_frequency_bound P Q _ _ l h X r
    hlpos hhpos hl hh hr hrect (((2*s*k : ℕ) : ℝ)⁻¹)
    (Real.exp (-(Real.log (Real.log m))^3/128))
    (((coprimeBlock m (pLog (Real.log m) k) (pWidth (Real.log m) k) A i).card : ℝ)*
      ((coprimeBlock m (qLog (Real.log m) s) (qWidth (Real.log m) s) A j).card : ℝ))
    (K*(harmonic m : ℝ)*(Real.log (Real.log m))^12) (Real.exp_pos _).le (by positivity)
    (by intro a b; simpa only [mul_assoc] using hbil a b)
    (hfreq x hlo hhi k s hkfirst hsfirst)
  convert hmain using 1 <;> ring

end NField.Alignment.KorolevActualSawtoothBlocks
