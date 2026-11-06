/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevActualSawtoothBlocks

/-! # Summing actual source sawtooth blocks over their residual support -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevActualResidualBound
open Filter KorolevActualSawtoothBlocks KorolevPrimeWindows KorolevWindowParameters
  KorolevActualPrimeBlocks KorolevLogarithmicPartition KaratsubaSourcePrimeBlocks
  KorolevCanonicalPrimeSlices KorolevBlockResidualVolume KorolevBlockResidualRange
  DedekindReciprocity DedekindInverseResidueTransform
open scoped Topology BigOperators Classical

/-- The raw prime block dominates its coprime population without changing the residual support. -/
theorem coprime_card_le (m : ℕ) (l D A : ℝ) (i : ℕ) :
    ((coprimeBlock m l D A i).card : ℝ) ≤ ((block l D A i).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ (block l D A i))

/-- Actual residual summation retains the cubic saving with a fixed endpoint-ratio cost. -/
theorem eventual_residual_block_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
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
      ∀ P Q : Finset ℕ, ∀ l X r : ℕ,
      0 < l → l.Coprime m → r.Coprime m →
      ‖∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
        primeSliceOn P Q
        (block (pLog (Real.log m) k) (pWidth (Real.log m) k) A i)
        (block (qLog (Real.log m) s) (qWidth (Real.log m) s) A j) l h X m
        (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))‖ ≤
        K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
          Real.exp (-(Real.log (Real.log m))^3/128)*
          (Real.exp (4*A)*(X : ℝ)/(l : ℝ)^2) := by
  obtain ⟨K, hK, hb⟩ := eventual_sawtooth_block_bound C hC A hA herror
  refine ⟨K, hK, ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc := Real.log_nonneg hC
  filter_upwards [hb,
    ht.eventually (eventual_parameters (Real.log C) hc A (by linarith)),
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) hc),
    hlog.eventually_gt_atTop 1]
    with m hsaw hp hfirst hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
      i j hi hj P Q l X r hlpos hl hr
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
  have hH : 0 ≤ (harmonic m : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic m := by unfold harmonic; positivity
    exact_mod_cast hQ
  let δ := K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
    Real.exp (-(Real.log (Real.log m))^3/128)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  apply norm_residual_sum_le P Q l X m hlpos _
    (pLog (Real.log m) k) (qLog (Real.log m) s)
    (by linarith : 0 < A) hkP.2.2.1 hsQ.2.2.2 hδ i j
  intro h hh
  obtain ⟨hhIcc, hsq, hhc⟩ := Finset.mem_filter.mp hh
  have hhpos : 0 < h := by have := (Finset.mem_Icc.mp hhIcc).1; omega
  have hbound := hsaw x hlo hhi k s hkfirst hklast hsfirst hslast i j hi hj
    P Q l h X r hlpos hhpos hl hhc hr
  apply hbound.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (coprime_card_le m _ _ _ _) hδ)
    (coprime_card_le m _ _ _ _) (by positivity) (by positivity)

end NField.Alignment.KorolevActualResidualBound
