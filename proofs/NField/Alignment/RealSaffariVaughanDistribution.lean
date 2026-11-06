/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SaffariVaughanDistribution

/-! # The printed Saffari–Vaughan estimate at arbitrary real cutoffs -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealSaffariVaughanDistribution
open scoped BigOperators Classical
open RealReciprocalPrefixEstimate ReciprocalDistributionConditional ReciprocalDyadicPartition
  ReciprocalLogComparison SaffariVaughanReciprocalTransfer WeightedFractionalPartTransfer

def realDistribution (X Y α : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,(n:ℝ)⁻¹*(if Int.fract (X/n)<α then 1 else 0)
def logScale (X : ℝ) : ℝ := Real.rpow (Real.log X) (2/3:ℝ)

theorem logScale_two_pos : 0<logScale 2 :=
  Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _

theorem logScale_mono {X : ℝ} (hX : 2≤X) : logScale 2≤logScale X := by
  exact Real.rpow_le_rpow (Real.log_nonneg (by norm_num))
    (Real.log_le_log (by norm_num) hX) (by norm_num)

theorem real_harmonic_correction {Y : ℝ} (hY : 1≤Y) :
    |(harmonic ⌊Y⌋₊:ℝ)-Real.log Y|≤1 := by
  have hl := log_le_harmonic_floor Y (by linarith)
  have hh := harmonic_floor_le_one_add_log Y hY
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem real_distribution_centered (X Y α : ℝ) :
    prefixSum (fun n => (n:ℝ)⁻¹*((if Int.fract (X/n)<α then 1 else 0)-α)) ⌊Y⌋₊=
      realDistribution X Y α-α*(harmonic ⌊Y⌋₊:ℝ) := by
  rw [prefixSum_eq_Icc]
  unfold realDistribution
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem real_distribution_error : ∃ K : ℝ,0<K ∧
    ∀ X Y α : ℝ,2≤Y → Y≤X → 0≤α → α≤1 →
      |realDistribution X Y α-α*Real.log Y|≤K*logScale X := by
  obtain ⟨C,hC,hR⟩ := reciprocal_prefix_estimate
  let K := distributionConstant C prefixDecay
  have hγ := prefixDecay_pos
  have hK : 0<K := by dsimp [K,distributionConstant]; positivity
  have hs0 := logScale_two_pos
  refine ⟨K+5/logScale 2,by positivity,?_⟩
  intro X Y α hY hYX hα0 hα1
  have hX : 2≤X := hY.trans hYX
  have hs := logScale_mono hX
  have hscale : 0≤logScale X := by linarith
  have hFY : (⌊Y⌋₊:ℝ)≤X := (Nat.floor_le (by linarith)).trans hYX
  have hfloor : 0<⌊Y⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hb : |realDistribution X Y α-α*(harmonic ⌊Y⌋₊:ℝ)|≤K*logScale X+4 := by
    rw [← real_distribution_centered]
    by_cases hX4 : 4≤X
    · have hh := centered_distribution_scale C prefixDecay hC.le prefixDecay_pos prefixDecay_le_one
        hR ⌊Y⌋₊ hfloor X α hX4 hFY hα0 hα1
      change _≤K*logScale X at hh
      linarith
    · have hfour : ⌊Y⌋₊≤4 := by
        have hlt : (⌊Y⌋₊:ℝ)<4 := by linarith
        have hlt' : ⌊Y⌋₊<4 := by exact_mod_cast hlt
        omega
      have hh := initial_centered_bound ⌊Y⌋₊ X α hα0 hα1
      rw [min_eq_left hfour] at hh
      exact hh.trans (by nlinarith)
  have hH : |α*((harmonic ⌊Y⌋₊:ℝ)-Real.log Y)|≤1 := by
    rw [abs_mul,abs_of_nonneg hα0]
    have := mul_le_mul hα1 (real_harmonic_correction (by linarith : 1≤Y))
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    simpa using this
  have hratio : 5≤5/logScale 2*logScale X := by
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0≤5/logScale 2)
    have he : 5/logScale 2*logScale 2=5 := by field_simp
    rwa [he] at hh
  calc
    _ = |(realDistribution X Y α-α*(harmonic ⌊Y⌋₊:ℝ))+
        α*((harmonic ⌊Y⌋₊:ℝ)-Real.log Y)| := by congr 1; ring
    _ ≤ |realDistribution X Y α-α*(harmonic ⌊Y⌋₊:ℝ)|+
        |α*((harmonic ⌊Y⌋₊:ℝ)-Real.log Y)| := abs_add_le _ _
    _ ≤ K*logScale X+5 := by linarith
    _ ≤ _ := by nlinarith

/-- Title: `Saffari–Vaughan distribution with arbitrary real cutoffs`. -/
theorem normalized_real_distribution : ∃ K : ℝ,0<K ∧
    ∀ X Y α : ℝ,2≤Y → Y≤X → 0≤α → α≤1 →
      |realDistribution X Y α/Real.log Y-α|≤
        K*(Real.log X)^(2/3:ℝ)/Real.log Y := by
  obtain ⟨K,hK,h⟩ := real_distribution_error
  refine ⟨K,hK,?_⟩
  intro X Y α hY hYX hα0 hα1
  have hlog : 0<Real.log Y := Real.log_pos (by linarith)
  rw [show realDistribution X Y α/Real.log Y-α=
    (realDistribution X Y α-α*Real.log Y)/Real.log Y by field_simp]
  rw [abs_div,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (h X Y α hY hYX hα0 hα1) hlog.le

end NField.Alignment.RealSaffariVaughanDistribution
