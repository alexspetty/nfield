/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalDistributionConditional
import NField.Alignment.SaffariVaughanFiniteReduction

/-! # Exact Saffari--Vaughan target from real reciprocal cancellation
The reciprocal-prefix estimate remains the explicit analytic dependency.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SaffariVaughanReciprocalTransfer
open ReciprocalDistributionConditional ReciprocalDyadicPartition
  SaffariVaughanFiniteReduction WeightedFractionalPartTransfer
open scoped BigOperators Classical

theorem prefixSum_eq_Icc {A : Type*} [AddCommMonoid A] (f : ℕ → A) (Y : ℕ) :
    prefixSum f Y = ∑ n ∈ Finset.Icc 1 Y, f n := by
  unfold prefixSum
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add']
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

/-- Exact correspondence with the rational remainder distribution used by the paper. -/
theorem rational_centered_identity (N d Y : ℕ) (α : ℝ) :
    prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (((N : ℝ)/d)/n) < α then 1 else 0)-α)) Y =
      weightedFractionalDistribution N d Y α - α*(harmonic Y : ℝ) := by
  rw [prefixSum_eq_Icc]
  have hH : (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH]
  unfold weightedFractionalDistribution
  simp_rw [quotient_eq_fract]
  simp only [Nat.cast_mul, ← div_div]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The Saffari--Vaughan distribution bound follows from the uniform real
reciprocal-prefix estimate, which is an explicit hypothesis here. -/
theorem saffari_vaughan_of_reciprocal (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hR : ReciprocalPrefixEstimate C γ) : SaffariVaughanDistributionEstimate := by
  let K := distributionConstant C γ
  have hK : 0 ≤ K := by dsimp [K, distributionConstant]; positivity
  refine ⟨K+5, by positivity, ?_⟩
  intro N d Y α hd hN hY hNY hα0 hα1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hYx : (Y : ℝ) ≤ (N : ℝ)/d := by
    apply (le_div_iff₀ hdR).mpr
    have hh : (d : ℝ)*Y ≤ N := by exact_mod_cast hNY
    nlinarith
  have hs := scale_ge_one N d hd hN
  have hcenter : |weightedFractionalDistribution N d Y α - α*(harmonic Y : ℝ)| ≤
      (K+4)*fractionalDistributionScale N d := by
    rw [← rational_centered_identity]
    by_cases hx : 4 ≤ (N : ℝ)/d
    · have hb := centered_distribution_scale C γ hC hγ hγ1 hR Y (by omega)
        ((N : ℝ)/d) α hx hYx hα0 hα1
      change _ ≤ K*fractionalDistributionScale N d at hb
      have hn : 0 ≤ fractionalDistributionScale N d := by linarith
      nlinarith
    · have hY4 : Y ≤ 4 := by
        have hh : (Y : ℝ) < 4 := by linarith
        have hh' : Y < 4 := by exact_mod_cast hh
        omega
      have hb := initial_centered_bound Y ((N : ℝ)/d) α hα0 hα1
      rw [min_eq_left hY4] at hb
      nlinarith
  have hh : |α*((harmonic Y : ℝ)-Real.log Y)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hα0]
    have ht := mul_le_mul hα1 (harmonic_correction Y (by omega)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using ht
  calc
    _ = |(weightedFractionalDistribution N d Y α-α*(harmonic Y : ℝ))+
        α*((harmonic Y : ℝ)-Real.log Y)| := by congr 1; ring
    _ ≤ |weightedFractionalDistribution N d Y α-α*(harmonic Y : ℝ)|+
        |α*((harmonic Y : ℝ)-Real.log Y)| := abs_add_le _ _
    _ ≤ (K+4)*fractionalDistributionScale N d+1 := add_le_add hcenter hh
    _ ≤ _ := by nlinarith

end NField.Alignment.SaffariVaughanReciprocalTransfer
