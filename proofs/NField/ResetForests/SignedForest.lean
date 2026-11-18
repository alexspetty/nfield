/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ForestSaturation
import NField.ResetForests.RawClock
/-! # Signed forest work with the complete original field

The selected reset source is its actual gcd-collapse fibre. The full clock
row, rather than absolute root readings, supplies its first-power work.
-/

noncomputable section

namespace NField.ResetForests.SignedForestWork

open scoped BigOperators
open NField.Alignment
open AbsoluteForestWork ClockRows PhasePopulations DedekindFourierMoment CommonResetDedekind

def forestSource (N D d : ℕ) : ℝ :=
  Core.collapseSource N (forestCarrier N D) (fun _ => 1) d

def restorationWork (N Q D : ℕ) : ℝ :=
  2*∑ d ∈ forestClocks N D, (1-forestSource N D d)*fullClock N Q d

theorem forest_source_bounds {N D d : ℕ} (hN : 0 < N)
    (hd : d ∈ forestClocks N D) :
    1 ≤ forestSource N D d ∧ forestSource N D d ≤ ((N/d : ℕ) : ℝ) := by
  obtain ⟨hdI, hrough⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd2, hdN⟩ := Finset.mem_Icc.mp hdI
  refine ⟨?_, Core.collapse_unit_le N (forestCarrier N D) d⟩
  exact Core.collapse_unit_ge_one (Finset.mem_Icc.mpr ⟨by omega, hdN⟩)
    ((forest_carrier_selection hN (by omega : 0 < d) hdN D).mp hrough)

theorem selected_forest_clock_identity {N : ℕ} (hN : 0 < N) (Q D : ℕ) :
    Core.selectedReading N Q (Core.forestMask N D) =
      2*∑ d ∈ forestClocks N D, forestSource N D d*fullClock N Q d := by
  rw [selected_forest_complete_source hN]
  change (2*∑ d ∈ Finset.Icc 1 N, forestSource N D d*fullClock N Q d)=_
  have h1 : forestSource N D 1*fullClock N Q 1=0 := by rw [full_clock_one, mul_zero]
  rw [← sum_Icc_remove_one N _ h1]
  unfold forestClocks
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hrough : Core.roughPart N d ∣ D
  · simp only [hrough, if_true]
  · have hdI := Finset.mem_Icc.mp hd
    have hnot : ¬d ∣ forestCarrier N D := by
      simpa only [← forest_carrier_selection hN (by omega : 0 < d) hdI.2 D] using hrough
    simp only [hrough, if_false, forestSource, Core.collapse_supported _ _ _ hnot, zero_mul]

theorem weighted_forest_clock_bound {p : ℕ} (hp : p.Prime) (D : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ forestClocks (p-1) D, |w d| ≤ (((p-1)/d : ℕ) : ℝ)) :
    |2*∑ d ∈ forestClocks (p-1) D, w d*fullClock (p-1) (p^2) d| ≤
      (((p-1 : ℕ) : ℝ)/2)*
        (∑ d ∈ forestClocks (p-1) D, (harmonic (d/2) : ℝ)^2) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2*(∑ d ∈ forestClocks (p-1) D, |w d*fullClock (p-1) (p^2) d|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ d ∈ forestClocks (p-1) D, 2*|w d| * |fullClock (p-1) (p^2) d| := by
      simp only [Finset.mul_sum, abs_mul, mul_assoc]
    _ ≤ ∑ d ∈ forestClocks (p-1) D,
        (((p-1 : ℕ) : ℝ)/2)*(harmonic (d/2) : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
      have hdp : d < p := lt_of_le_of_lt hdI.2 (Nat.sub_lt hp.pos (by decide))
      have hwd : |w d| *(d : ℝ) ≤ ((p-1 : ℕ) : ℝ) := by
        calc
          _ ≤ (((p-1)/d : ℕ) : ℝ)*(d : ℝ) :=
            mul_le_mul_of_nonneg_right (hw d hd) (Nat.cast_nonneg _)
          _ ≤ _ := by exact_mod_cast Nat.div_mul_le_self (p-1) d
      calc
        _ ≤ 2*|w d| *((d : ℝ)/4*(harmonic (d/2) : ℝ)^2) :=
          mul_le_mul_of_nonneg_left (whole_clock_work_bound hp hdI.1 hdp) (by positivity)
        _ = (|w d| *(d : ℝ))/2*(harmonic (d/2) : ℝ)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hwd (by norm_num)) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem signed_forest_and_restoration_finite {p : ℕ} (hp : p.Prime) (D : ℕ) :
    |Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) D)| ≤
      (((p-1 : ℕ) : ℝ)/2)*
        (∑ d ∈ forestClocks (p-1) D, (harmonic (d/2) : ℝ)^2) ∧
    |restorationWork (p-1) (p^2) D| ≤
      (((p-1 : ℕ) : ℝ)/2)*
        (∑ d ∈ forestClocks (p-1) D, (harmonic (d/2) : ℝ)^2) := by
  have hN : 0 < p-1 := by have := hp.two_le; omega
  constructor
  · rw [selected_forest_clock_identity hN]
    apply weighted_forest_clock_bound hp
    intro d hd
    have hb := forest_source_bounds hN hd
    rw [abs_of_nonneg (by linarith : 0 ≤ forestSource (p-1) D d)]
    exact hb.2
  · apply weighted_forest_clock_bound hp
    intro d hd
    have hb := forest_source_bounds hN hd
    rw [abs_of_nonpos (by linarith : 1-forestSource (p-1) D d ≤ 0)]
    linarith

theorem complete_clock_interior_sum (N Q : ℕ) :
    CommonResetSampling.interiorSource N Q=2*∑ d ∈ Finset.Icc 2 N, fullClock N Q d := by
  rw [CommonResetDedekind.interiorSource_coefficient_sum]
  rw [CommonResetDedekind.sum_Icc_remove_one N (fullClock N Q) (full_clock_one N Q)]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  unfold fullClock Core.completeCorrelation
  apply Finset.sum_congr rfl
  intro j _
  rw [CommonResetBernoulliLifts.coefficient_swap Q j d]

theorem other_forest_restoration_identity {N : ℕ} (hN : 0 < N) (Q D : ℕ) :
    Core.selectedReading N Q (fun k => !(Core.forestMask N D k)) =
      2*(∑ d ∈ Finset.Icc 2 N, if Core.forestMask N D d then 0 else fullClock N Q d)+
        restorationWork N Q D := by
  have hall := complete_clock_interior_sum N Q
  rw [Core.forest_complement_split N Q (Core.forestMask N D), selected_forest_clock_identity hN] at hall
  have hsplit : (∑ d ∈ Finset.Icc 2 N, fullClock N Q d) =
      (∑ d ∈ Finset.Icc 2 N, if Core.forestMask N D d then 0 else fullClock N Q d)+
        ∑ d ∈ forestClocks N D, fullClock N Q d := by
    unfold forestClocks
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : Core.roughPart N d ∣ D <;> simp [Core.forestMask, h]
  rw [hsplit] at hall
  have hr : restorationWork N Q D=
      2*(∑ d ∈ forestClocks N D, fullClock N Q d)-
        2*(∑ d ∈ forestClocks N D, forestSource N D d*fullClock N Q d) := by
    unfold restorationWork
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, mul_sub]
  rw [hr]
  linarith

end NField.ResetForests.SignedForestWork
