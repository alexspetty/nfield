/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedSampling

/-! # Coprime active weights and independent unweighted grids -/

noncomputable section

namespace NField.Alignment.CommonResetAllGrids

open scoped BigOperators
open CommonResetGram CommonResetSampling CommonResetWeightedSources CommonResetWeightedSampling

theorem resetMass_coprime {N q : ℕ} (hq : 0 < q) (c : ℕ → ℝ)
    (hcop : ∀ j ∈ Finset.Icc 1 N, c j ≠ 0 → q.Coprime j) :
    resetMass N q c = (∑ j ∈ Finset.Icc 1 N, c j)^2 := by
  rw [resetMass_gcd_sum hq, pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : c j = 0
  · simp only [hc, zero_mul]
  · have hg : (j.gcd k).gcd q = 1 :=
      ((hcop j hj hc).symm.coprime_dvd_left (Nat.gcd_dvd_left j k)).gcd_eq_one
    simp only [hg, Nat.cast_one, mul_one]

theorem curvatureMoment_coprime {N q : ℕ} (c : ℕ → ℝ)
    (hcop : ∀ j ∈ Finset.Icc 1 N, c j ≠ 0 → q.Coprime j) :
    curvatureMoment N q c = ∑ j ∈ Finset.Icc 1 N, c j/j := by
  unfold curvatureMoment
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : c j = 0
  · simp only [hc, zero_mul, zero_div]
  · simp only [(hcop j hj hc).symm.gcd_eq_one, Nat.cast_one, one_pow, mul_one]

/-- Title: `Coprime active clocks leave only the common reset square`. -/
theorem coprime_weighted_sampling {N q : ℕ} (hq : 0 < q) (c : ℕ → ℝ)
    (hcop : ∀ j ∈ Finset.Icc 1 N, c j ≠ 0 → q.Coprime j) :
    weightedDefect N q c = (∑ j ∈ Finset.Icc 1 N, c j)^2/q +
      4*weightedInterior N q c/q -
      2*slopeMoment N c*(∑ j ∈ Finset.Icc 1 N, c j/j)/(3*(q : ℝ)^2) := by
  rw [weighted_sampling_identity hq, resetMass_coprime hq c hcop,
    curvatureMoment_coprime c hcop]

theorem resetWeight_one (N d : ℕ) : resetWeight N (fun _ => 1) d = (N/d : ℕ) := by
  unfold resetWeight
  rw [← Finset.sum_filter]
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div]

theorem weightedInterior_one (N q : ℕ) : weightedInterior N q (fun _ => 1) = interiorSource N q := by
  simp only [weightedInterior, resetWeight_one, unit_weights, interiorSource]

theorem weightedDefect_one (N q : ℕ) : weightedDefect N q (fun _ => 1) = defect N q := by
  simp only [weightedDefect, weightedSample, unit_weights, defect, continuousEnergy, sampledEnergy]

theorem slopeMoment_one (N : ℕ) : slopeMoment N (fun _ => 1) = (N : ℝ)*(N+1)/2 := by
  induction N with
  | zero => simp [slopeMoment]
  | succ N ih =>
    rw [slopeMoment, Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
    change slopeMoment N (fun _ => 1) + (↑(N+1) : ℝ)*1 = _
    rw [ih]
    push_cast
    ring

/-- Title: `Independent clock and grid sizes retain every aligned reset`. -/
theorem all_grid_unweighted {q : ℕ} (hq : 0 < q) (N : ℕ) :
    defect N q =
      (∑ d ∈ q.divisors.filter (fun d => d ≤ N), (d.totient : ℝ)*((N/d : ℕ) : ℝ)^2)/q +
      4*interiorSource N q/q -
      (N : ℝ)*(N+1)/(3*(q : ℝ)^2)*∑ j ∈ Finset.Icc 1 N, (j.gcd q : ℝ)^2/j := by
  rw [← weightedDefect_one, weighted_sampling_identity hq, weightedInterior_one, slopeMoment_one]
  simp only [resetMass, resetWeight_one, curvatureMoment, one_mul]
  ring

/-- Title: `Coprime independent grids have the exact harmonic curvature correction`. -/
theorem independent_coprime_sampling {N q : ℕ} (hq : 0 < q)
    (hcop : ∀ j ∈ Finset.Icc 1 N, q.Coprime j) :
    defect N q = (N : ℝ)^2/q + 4*interiorSource N q/q -
      (N : ℝ)*(N+1)*(harmonic N : ℝ)/(3*(q : ℝ)^2) := by
  rw [← weightedDefect_one, coprime_weighted_sampling hq (fun _ => 1) (fun j hj _ => hcop j hj),
    weightedInterior_one, slopeMoment_one]
  have hsum : (∑ j ∈ Finset.Icc 1 N, (1 : ℝ)/j) = (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  ring

end NField.Alignment.CommonResetAllGrids
