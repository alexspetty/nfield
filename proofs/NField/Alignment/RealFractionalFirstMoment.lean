/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSaffariVaughanDistribution

/-! # Uniform first fractional moments at real endpoints -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealFractionalFirstMoment
open scoped BigOperators Classical
open MeasureTheory RealSaffariVaughanDistribution WeightedFractionalPartTransfer

def realFirstMoment (X Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,(n:ℝ)⁻¹*Int.fract (X/n)

theorem real_distribution_integrable (X Y : ℝ) :
    IntervalIntegrable (realDistribution X Y) volume 0 1 := by
  unfold realDistribution
  have h := IntervalIntegrable.sum (Finset.Icc 1 ⌊Y⌋₊) fun n hn =>
    (intervalIntegrable_threshold_indicator (Int.fract (X/n))).const_mul ((n:ℝ)⁻¹)
  apply h.congr
  intro α hα
  simp only [Finset.sum_apply]

theorem integral_real_distribution (X Y : ℝ) :
    (∫ α in (0:ℝ)..1,realDistribution X Y α)=(harmonic ⌊Y⌋₊:ℝ)-realFirstMoment X Y := by
  unfold realDistribution realFirstMoment
  rw [intervalIntegral.integral_finsetSum]
  · simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul,integral_threshold_indicator
      (Int.fract_nonneg _) (Int.fract_lt_one _).le]
    ring
  · intro n hn
    exact (intervalIntegrable_threshold_indicator (Int.fract (X/n))).const_mul _

theorem real_distribution_integrated_error : ∃ K : ℝ,0<K ∧
    ∀ X Y : ℝ,2≤Y → Y≤X →
      |(harmonic ⌊Y⌋₊:ℝ)-realFirstMoment X Y-(1/2:ℝ)*Real.log Y|≤K*logScale X := by
  obtain ⟨K,hK,h⟩ := real_distribution_error
  refine ⟨K,hK,?_⟩
  intro X Y hY hYX
  have hlin : IntervalIntegrable (fun α : ℝ => α*Real.log Y) volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 1
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=1) (f:=fun α => realDistribution X Y α-α*Real.log Y)
    (C:=K*logScale X) (by
      intro α hα
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hα
      simpa only [Real.norm_eq_abs] using h X Y α hY hYX hα.1.le hα.2)
  rw [intervalIntegral.integral_sub (real_distribution_integrable X Y) hlin,
    integral_real_distribution,intervalIntegral.integral_mul_const,integral_id] at hi
  norm_num at hi
  simpa only [div_eq_mul_inv,mul_comm] using hi

/-- Title: `Uniform first fractional moment at real cutoffs`. -/
theorem real_first_moment_error : ∃ K : ℝ,0<K ∧
    ∀ X Y : ℝ,2≤Y → Y≤X →
      |realFirstMoment X Y-(1/2:ℝ)*Real.log Y|≤K*(Real.log X)^(2/3:ℝ) := by
  obtain ⟨K,hK,h⟩ := real_distribution_integrated_error
  have hs0 := logScale_two_pos
  refine ⟨K+1/logScale 2,by positivity,?_⟩
  intro X Y hY hYX
  have hb := h X Y hY hYX
  have hH := real_harmonic_correction (by linarith : 1≤Y)
  have hs := logScale_mono (hY.trans hYX)
  have hratio : 1≤1/logScale 2*logScale X := by
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0≤1/logScale 2)
    have he : 1/logScale 2*logScale 2=1 := by field_simp
    rwa [he] at hh
  calc
    _ = |-((harmonic ⌊Y⌋₊:ℝ)-realFirstMoment X Y-(1/2:ℝ)*Real.log Y)+
        ((harmonic ⌊Y⌋₊:ℝ)-Real.log Y)| := by congr 1; ring
    _ ≤ |(harmonic ⌊Y⌋₊:ℝ)-realFirstMoment X Y-(1/2:ℝ)*Real.log Y|+
        |(harmonic ⌊Y⌋₊:ℝ)-Real.log Y| := by
      simpa only [abs_neg] using (abs_add_le
        (-((harmonic ⌊Y⌋₊:ℝ)-realFirstMoment X Y-(1/2:ℝ)*Real.log Y))
        ((harmonic ⌊Y⌋₊:ℝ)-Real.log Y))
    _ ≤ K*logScale X+1 := by linarith
    _ ≤ _ := by change _≤(K+1/logScale 2)*logScale X; nlinarith

end NField.Alignment.RealFractionalFirstMoment
