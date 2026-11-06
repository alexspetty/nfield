/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevTupleBlockCount
import NField.Alignment.KorolevActualBlockCount
import NField.Alignment.KorolevActualResidualBound

/-! # Uniform norm bound for the complete actual canonical tuple sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalTupleBound
open Filter KorolevPrimeWindows KorolevWindowParameters KorolevActualPrimeBlocks
  KorolevLogarithmicPartition KorolevCanonicalPrimeSlices KorolevCanonicalTuples
  KorolevSourceWindowCount DedekindReciprocity DedekindInverseResidueTransform
open scoped Topology BigOperators Classical

/-- All selected windows, actual blocks, residuals and square factors are summed uniformly. -/
theorem eventual_canonical_tuple_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ B X r : ℕ, r.Coprime m →
      ‖∑ t ∈ (tuples (sourcePPrimes C m x) (sourceQPrimes C m x) B X).filter
        (fun t => (value t).Coprime m),
        ((rationalSawtooth (r*inverseResidue (value t) m) m : ℚ) : ℂ)‖ ≤
        2*K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
          Real.exp (-(Real.log (Real.log m))^3/128)*Real.exp (4*A)*(X : ℝ)*(Real.log m)^4 := by
  obtain ⟨K, hK, hresid⟩ := KorolevActualResidualBound.eventual_residual_block_bound C hC A hA herror
  refine ⟨K, hK, ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc := Real.log_nonneg hC
  filter_upwards [hresid, KorolevActualBlockCount.eventual_source_counts C hC A hA,
    ht.eventually (KorolevWindowParameters.eventual_window_conditions (Real.log C) hc),
    ht.eventually (eventual_parameters (Real.log C) hc A (by linarith)),
    hlog.eventually_gt_atTop 1]
    with m hrange hcounts hwin hp hL inst x hlo hhi B X r hr
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := source_log_range hmR hL hlo hhi
  have hw := hwin (Real.log (Real.log x)) hulo hule
  have hparams := hp (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hw hparams
  have hcoord : Real.exp (Real.log (Real.log m)) = Real.log m :=
    Real.exp_log (by linarith : 0 < Real.log (m : ℝ))
  rw [hcoord] at hparams
  let a := pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)
  let b := pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)
  let c := qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)
  let d := qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)
  let P := sourcePPrimes C m x
  let Q := sourceQPrimes C m x
  have hP : P = selectedPrimes (Real.log m) a b := by
    simp only [P, sourcePPrimes, KorolevParameterCount.pPrimes, hcoord, a, b]
  have hQ : Q = KorolevPrimeIntervals.intervalPrimes
      (upperEndpoint (Real.log m) (d+1)) (upperEndpoint (Real.log m) c) := by
    simp only [Q, sourceQPrimes, KorolevParameterCount.qPrimes, hcoord, c, d]
  have hDp : ∀ k ∈ Finset.Icc a b, A ≤ pWidth (Real.log m) k := by
    intro k hk
    have hkpos : 1 ≤ k := hw.1.first_pos.trans (Finset.mem_Icc.mp hk).1
    exact (hparams k hkpos (Or.inl (Finset.mem_Icc.mp hk).2)).2.2.1
  have hDq : ∀ s ∈ Finset.Icc c d, A ≤ qWidth (Real.log m) s := by
    intro s hs
    have hspos : 1 ≤ s := hw.2.first_pos.trans (Finset.mem_Icc.mp hs).1
    exact (hparams s hspos (Or.inr (Finset.mem_Icc.mp hs).2)).2.2.2
  have hH : 0 ≤ (harmonic m : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic m := by unfold harmonic; positivity
    exact_mod_cast hQ
  let D := K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
    Real.exp (-(Real.log (Real.log m))^3/128)*Real.exp (4*A)*(X : ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hnorm := KorolevTupleBlockCount.norm_nested_le (Finset.Icc a b) (Finset.Icc c d)
    B m (fun k => blockCount (pWidth (Real.log m) k) A)
    (fun s => blockCount (qWidth (Real.log m) s) A)
    (fun l k s i j => ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
      primeSliceOn P Q (block (pLog (Real.log m) k) (pWidth (Real.log m) k) A i)
        (block (qLog (Real.log m) s) (qWidth (Real.log m) s) A j) l h X m
        (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))) D hD (by
      intro l hl k hk s hs i hi j hj
      obtain ⟨hlIcc, hlc⟩ := Finset.mem_filter.mp hl
      have hlpos : 0 < l := by have := (Finset.mem_Icc.mp hlIcc).1; omega
      have hh := hrange x hlo hhi k s (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
        (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 i j
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) P Q l X r hlpos hlc hr
      convert hh using 1 <;> dsimp only [D] <;> ring)
  have hpop := hcounts x hlo hhi
  have hfull := KorolevActualTupleBlocks.sum_tuples_eq_blocks P Q B X m
    (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))
    (by linarith : 0 ≤ Real.log (m : ℝ)) (by linarith : 0 < A)
    hw.1.first_pos hw.2.first_pos hw.2.ordered hP hQ hDp hDq
  rw [hfull]
  apply hnorm.trans
  calc
    _ ≤ 2*D*(Real.log m)^2*(Real.log m)^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpop.1 (by positivity)) hpop.2
        (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
    _ = _ := by dsimp only [D]; ring

end NField.Alignment.KorolevCanonicalTupleBound
