/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SamplingPositive
/-! # Positivity of the literal continuous and sampled work

The finite sampled recovery also proves continuous faithfulness. At each
nonorigin prime-square sample every source wave is continuous. Zero
continuous square work forces these readings to vanish, and then the
already proved reset-mass reconstruction forces the source to vanish.
-/

noncomputable section

namespace NField.ResetForests.SourceMetrics

open scoped BigOperators Topology
open Filter MeasureTheory Set
open NField.Alignment CommonResetGram CollisionRampEnergy

theorem continuous_at_ae_zero {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hc : ContinuousAt f x) (hz : f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0) : f x=0 := by
  by_contra hne
  have hnull : volume {y : ℝ | y ∈ Ioc (0 : ℝ) 1 ∧ f y ≠ 0}=0 := by
    have h := ae_imp_of_ae_restrict hz
    simpa only [ae_iff, Classical.not_imp, Pi.zero_apply] using h
  have hnbhd : {y : ℝ | y ∈ Ioc (0 : ℝ) 1 ∧ f y ≠ 0} ∈ 𝓝 x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2, hc.eventually (eventually_ne_nhds hne)] with y hy hfy
    exact ⟨⟨hy.1, hy.2.le⟩, hfy⟩
  have hp := volume.measure_pos_of_mem_nhds hnbhd
  rw [hnull] at hp
  exact (lt_irrefl 0) hp

theorem midpoint_grid_continuousAt {Q j a : ℕ} (hQ : 0 < Q)
    (hj : j.Coprime Q) (ha : 0 < a) (haQ : a < Q) :
    ContinuousAt (midpointRow j) ((a : ℝ)/(Q : ℝ)) := by
  have hfr : Int.fract ((j : ℝ)*((a : ℝ)/(Q : ℝ))) ≠ 0 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]
    exact div_ne_zero (by exact_mod_cast grid_numerator_remainder_ne_zero hQ hj ha haQ)
      (by exact_mod_cast hQ.ne')
  have hfloor : (j : ℝ)*((a : ℝ)/(Q : ℝ)) ≠
      (⌊(j : ℝ)*((a : ℝ)/(Q : ℝ))⌋ : ℤ) := by
    exact sub_ne_zero.mp hfr
  have hf := (continuousAt_fract hfloor).comp (continuousAt_const.mul continuousAt_id)
  have he : midpointRow j =ᶠ[𝓝 ((a : ℝ)/(Q : ℝ))] affineRow j := by
    filter_upwards [hf.eventually (eventually_ne_nhds hfr)] with x hx
    change Int.fract ((j : ℝ)*x) ≠ 0 at hx
    simp only [midpointRow, hx, if_false]
  exact (hf.sub continuousAt_const).congr_of_eventuallyEq he

theorem weighted_grid_continuousAt (N Q : ℕ) (c : ℕ → ℝ) (a : ℕ)
    (hQ : 0 < Q) (ha : 0 < a) (haQ : a < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) :
    ContinuousAt (weightedProfile N c) ((a : ℝ)/(Q : ℝ)) := by
  unfold weightedProfile
  apply ContinuousAt.const_mul
  apply tendsto_finsetSum
  intro j hj
  exact continuousAt_const.mul (midpoint_grid_continuousAt hQ (hunit j hj) ha haQ)

theorem weighted_square_interval_integrable (N : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => weightedProfile N c x^2) volume a b := by
  have hint (j k : ℕ) (hj : j ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => (c j*c k)*(midpointRow j x*midpointRow k x)) volume a b :=
    (midpointProduct_intervalIntegrable (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1 a b).const_mul _
  simp_rw [weightedProfile_square]
  exact ⟨(integrable_finsetSum _ (fun j hj =>
      integrable_finsetSum _ (fun k hk => (hint j k hj hk).1))).const_mul 4,
    (integrable_finsetSum _ (fun j hj =>
      integrable_finsetSum _ (fun k hk => (hint j k hj hk).2))).const_mul 4⟩

theorem zero_continuous_work_grid {N Q : ℕ} (c : ℕ → ℝ) (hQ : 0 < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q)
    (hz : (∫ x in (0 : ℝ)..1, weightedProfile N c x^2)=0) :
    ∀ a ∈ Finset.range Q, weightedProfile N c ((a : ℝ)/(Q : ℝ))=0 := by
  have hae : (fun x => weightedProfile N c x^2) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (by norm_num)
      (Eventually.of_forall (fun x => sq_nonneg (weightedProfile N c x)))
      (weighted_square_interval_integrable N c 0 1)).mp hz
  intro a ha
  have haQ : a < Q := Finset.mem_range.mp ha
  by_cases ha0 : a=0
  · subst a
    simp [weightedProfile, midpointRow]
  · have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hx : (a : ℝ)/(Q : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos haR hQR, (div_lt_one hQR).mpr (by exact_mod_cast haQ)⟩
    have he := continuous_at_ae_zero hx
      ((weighted_grid_continuousAt N Q c a hQ (Nat.pos_of_ne_zero ha0) haQ hunit).pow 2) hae
    exact sq_eq_zero_iff.mp he

theorem continuous_work_positive {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (c : ℕ → ℝ) (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q)
    (hne : ∃ j ∈ Finset.Icc 1 N, c j ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, weightedProfile N c x^2 := by
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, weightedProfile N c x^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hg := zero_continuous_work_grid c (by omega) hunit hz.symm
  have hc := sampled_field_injective hN hQ c hunit hg
  obtain ⟨j, hj, hjc⟩ := hne
  exact hjc (hc j hj)

theorem sampled_work_positive {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (c : ℕ → ℝ) (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q)
    (hne : ∃ j ∈ Finset.Icc 1 N, c j ≠ 0) :
    0 < ∑ a ∈ Finset.range Q, weightedProfile N c ((a : ℝ)/(Q : ℝ))^2 := by
  have hs : ∃ a ∈ Finset.range Q, weightedProfile N c ((a : ℝ)/(Q : ℝ)) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hc := sampled_field_injective hN hQ c hunit hh
    obtain ⟨j, hj, hjc⟩ := hne
    exact hjc (hc j hj)
  obtain ⟨a, ha, hac⟩ := hs
  exact Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨a, ha, sq_pos_of_ne_zero hac⟩

end NField.ResetForests.SourceMetrics
