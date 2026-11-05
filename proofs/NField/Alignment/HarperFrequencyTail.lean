/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyConditioning

/-!
# The distant frequency contribution

Split the actual conditioned frequency sum into a finite central set and
its complete complement. The exact interval second moment controls the
complement. Factoring the summable 3/2 weight proves a uniform tail bound
of order (V+1)^(-1/3); at the manuscript cutoff log(P)^(1/100), this gives
the explicit log(P)^(-1/300) saving. No central-interval saving is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFrequencyTail

open scoped BigOperators Topology
open MeasureTheory Set Filter SteinhausMoment HarperEulerIntegral HarperFrequencyIntervals
  HarperFrequencyConditioning HarperSmoothingConditioning HarperActualConditioning
  HarperWeightedConditioning HarperConditioningFrequencies HarperRoundedCutoff
  CollisionMertensInput

def centralFrequencies (V : ℝ) : Finset ℤ := Finset.Icc ⌈-V⌉ ⌊V⌋
def tailFrequencies (V : ℝ) : Set ℤ := {v | V < |(v : ℝ)|}
def frequencyTail (V : ℝ) : ℝ := ∑' v : tailFrequencies V, frequencyWeight (3/2) v
def tailConstant : ℝ := ∑' v : ℤ, frequencyWeight (7/6) v

theorem centralFrequencies_mem (V : ℝ) (v : ℤ) : v ∈ centralFrequencies V ↔ |(v : ℝ)| ≤ V := by
  simp [centralFrequencies, Int.ceil_le, Int.le_floor, abs_le]

theorem tailFrequencies_eq_compl (V : ℝ) : tailFrequencies V = (centralFrequencies V : Set ℤ)ᶜ := by
  ext v
  simp [tailFrequencies, centralFrequencies_mem]

theorem frequencyWeight_factor (v : ℤ) :
    frequencyWeight (3/2) v = (|(v : ℝ)|+1)^(-(1/3 : ℝ))*frequencyWeight (7/6) v := by
  unfold frequencyWeight
  simp only [one_div, ← Real.rpow_neg (by positivity : 0 ≤ |(v : ℝ)|+1)]
  rw [← Real.rpow_add (by positivity)]
  norm_num

theorem frequencyTail_point {V : ℝ} (hV : 0 ≤ V) (v : tailFrequencies V) :
    frequencyWeight (3/2) v ≤ (V+1)^(-(1/3 : ℝ))*frequencyWeight (7/6) v := by
  rw [frequencyWeight_factor]
  apply mul_le_mul_of_nonneg_right _ (frequencyWeight_nonneg _ _)
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (add_le_add v.property.le le_rfl) (by norm_num)

theorem frequencyTail_bound {V : ℝ} (hV : 0 ≤ V) :
    frequencyTail V ≤ (V+1)^(-(1/3 : ℝ))*tailConstant := by
  have h3 := frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)
  have h7 := frequencyWeight_summable (by norm_num : (1 : ℝ) < 7/6)
  calc
    _ ≤ ∑' v : tailFrequencies V, (V+1)^(-(1/3 : ℝ))*frequencyWeight (7/6) v :=
      Summable.tsum_le_tsum (frequencyTail_point hV) (h3.subtype _) ((h7.subtype _).mul_left _)
    _ = (V+1)^(-(1/3 : ℝ))*(∑' v : tailFrequencies V, frequencyWeight (7/6) v) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.tsum_subtype_le (frequencyWeight (7/6)) (tailFrequencies V)
        (fun v => frequencyWeight_nonneg _ v) h7)
      (Real.rpow_nonneg (by positivity) _)

theorem frequencyTail_nonneg (V : ℝ) : 0 ≤ frequencyTail V :=
  tsum_nonneg (fun v => frequencyWeight_nonneg _ v)

theorem tailConstant_nonneg : 0 ≤ tailConstant := tsum_nonneg (frequencyWeight_nonneg _)

theorem weighted_tail_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P V : ℝ) :
    (∑' v : tailFrequencies V, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) ≤
      (inversePrimeProduct P)^(3/4 : ℝ)*frequencyTail V := by
  calc
    _ ≤ ∑' v : tailFrequencies V, (inversePrimeProduct P)^(3/4 : ℝ)*frequencyWeight (3/2) v := by
      apply Summable.tsum_le_tsum _ ((unitEnergy_weighted_conditioning_summable hell c1 c2 P).subtype _)
        (((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).subtype _).mul_left _)
      intro v
      exact (mul_le_mul_of_nonneg_left (unitEnergy_conditioning_bound hell c1 c2 P v)
        (frequencyWeight_nonneg _ _)).trans_eq (mul_comm _ _)
    _ = _ := tsum_mul_left

theorem weighted_frequency_split {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P V : ℝ) :
    (∑' v : ℤ, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) =
      (∑ v ∈ centralFrequencies V, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) +
      ∑' v : tailFrequencies V, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v) := by
  rw [tailFrequencies_eq_compl]
  exact (unitEnergy_weighted_conditioning_summable hell c1 c2 P).sum_add_tsum_compl.symm

theorem spectral_conditioning_split {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P V : ℝ) :
    boxConditioning p c1 c2 (spectralIntegral P (1/2)) ≤ (16 : ℝ)^(3/4 : ℝ)*
      ((∑ v ∈ centralFrequencies V, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) +
       (inversePrimeProduct P)^(3/4 : ℝ)*frequencyTail V) := by
  have h := spectral_conditioning_localized hell c1 c2 P
  rw [weighted_frequency_split hell c1 c2 P V] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (weighted_tail_bound hell c1 c2 P V))
    (Real.rpow_nonneg (by norm_num) _))

theorem spectral_conditioning_tail_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    boxConditioning p c1 c2 (spectralIntegral P (1/2)) ≤ (16 : ℝ)^(3/4 : ℝ)*
      ((∑ v ∈ centralFrequencies V, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) +
       (inversePrimeProduct P)^(3/4 : ℝ)*((V+1)^(-(1/3 : ℝ))*tailConstant)) := by
  exact (spectral_conditioning_split hell c1 c2 P V).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (frequencyTail_bound hV) (Real.rpow_nonneg (inversePrimeProduct_pos P).le _)))
      (Real.rpow_nonneg (by norm_num) _))

def frequencyCutoff (P : ℝ) : ℝ := (Real.log P)^(1/100 : ℝ)

theorem frequencyCutoff_nonneg {P : ℝ} (hP : 0 ≤ Real.log P) : 0 ≤ frequencyCutoff P :=
  Real.rpow_nonneg hP _

theorem cutoff_tail_bound {P : ℝ} (hP : 0 < Real.log P) :
    frequencyTail (frequencyCutoff P) ≤ (Real.log P)^(-(1/300 : ℝ))*tailConstant := by
  calc
    _ ≤ (frequencyCutoff P+1)^(-(1/3 : ℝ))*tailConstant := frequencyTail_bound (frequencyCutoff_nonneg hP.le)
    _ ≤ (frequencyCutoff P)^(-(1/3 : ℝ))*tailConstant :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hP _) (by linarith) (by norm_num)) tailConstant_nonneg
    _ = _ := by
      unfold frequencyCutoff
      rw [← Real.rpow_mul hP.le]
      norm_num

end NField.Alignment.HarperFrequencyTail
