/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTheorem

/-!
# The Jordan summability criterion for general positive age masses

This file proves the equivalence for the actual finite Haar potentials.
The separate equivalence with existence of any coboundary potential has
additional Fourier obligations and is not asserted by this result.
-/

noncomputable section

namespace NField.Alignment.CollisionGeneralWeightCriterion

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionJordanVariance

def generalAmplitude (v : ℕ → ℝ) (q : ℕ) : ℝ := ∑' k, if q ∣ k then v k else 0

def generalEnergy (v : ℕ → ℝ) (q : ℕ) : ℝ :=
  if 2 ≤ q then jordanTwo q * (generalAmplitude v q)^2 else 0

def generalFiniteEnergy (v : ℕ → ℝ) (M q : ℕ) : ℝ :=
  if 2 ≤ q then jordanTwo q * (finiteAmplitude v q M)^2 else 0

theorem generalAmplitude_summable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : Summable v) (q : ℕ) : Summable (fun k => if q ∣ k then v k else 0) := by
  apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hv])
    (fun k => by split_ifs <;> simp [hv]) hs

theorem generalAmplitude_tendsto (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) (q : ℕ) :
    Tendsto (finiteAmplitude v q) atTop (nhds (generalAmplitude v q)) := by
  have h := (generalAmplitude_summable v hv hs q).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hz : (if q ∣ 0 then v 0 else 0) = 0 := by simp [h0]
  have ho : (if q ∣ 1 then v 1 else 0) = 0 := by simp [h1]
  have hsum (M : ℕ) : (∑ k ∈ Finset.range (M+1), if q ∣ k then v k else 0) =
      finiteAmplitude v q M := sum_range_zero_one (fun k => if q ∣ k then v k else 0) hz ho M
  simpa only [Function.comp_def, hsum, generalAmplitude] using h

theorem generalFiniteEnergy_nonneg (v : ℕ → ℝ) (M q : ℕ) :
    0 ≤ generalFiniteEnergy v M q := by
  unfold generalFiniteEnergy
  split_ifs
  · exact mul_nonneg (jordanTwo_nonneg q) (sq_nonneg _)
  · rfl

theorem generalEnergy_nonneg (v : ℕ → ℝ) (q : ℕ) : 0 ≤ generalEnergy v q := by
  unfold generalEnergy
  split_ifs
  · exact mul_nonneg (jordanTwo_nonneg q) (sq_nonneg _)
  · rfl

theorem generalFiniteEnergy_le (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : Summable v) (M q : ℕ) : generalFiniteEnergy v M q ≤ generalEnergy v q := by
  have hnon : 0 ≤ finiteAmplitude v q M := Finset.sum_nonneg (fun k _ => by
    split_ifs <;> simp [hv])
  have hle : finiteAmplitude v q M ≤ generalAmplitude v q :=
    (generalAmplitude_summable v hv hs q).sum_le_tsum (Finset.Icc 2 M)
      (fun k _ => by split_ifs <;> simp [hv])
  unfold generalFiniteEnergy generalEnergy
  split_ifs
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hle 2) (jordanTwo_nonneg q)
  · rfl

theorem generalFiniteEnergy_tendsto (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) (q : ℕ) :
    Tendsto (fun M => generalFiniteEnergy v M q) atTop (nhds (generalEnergy v q)) := by
  unfold generalFiniteEnergy generalEnergy
  split_ifs
  · exact ((generalAmplitude_tendsto v hv h0 h1 hs q).pow 2).const_mul _
  · exact tendsto_const_nhds

theorem generalFiniteEnergy_support (v : ℕ → ℝ) (M q : ℕ) (hq : q ∉ Finset.Icc 2 M) :
    generalFiniteEnergy v M q = 0 := by
  unfold generalFiniteEnergy
  split_ifs with hq2
  · have hz : finiteAmplitude v q M = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkp := Finset.mem_Icc.mp hk
      have hqk : ¬ q ∣ k := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < k) hd
        exact hq (Finset.mem_Icc.mpr ⟨hq2, by omega⟩)
      exact if_neg hqk
    rw [hz, sq, mul_zero, mul_zero]
  · rfl

theorem generalFiniteEnergy_hasSum (v : ℕ → ℝ) (M : ℕ) :
    HasSum (generalFiniteEnergy v M) (27 * ‖finitePotential v M‖^2) := by
  have h : HasSum (generalFiniteEnergy v M)
      (∑ q ∈ Finset.Icc 2 M, generalFiniteEnergy v M q) :=
    hasSum_sum_of_ne_finset_zero (fun q hq => generalFiniteEnergy_support v M q hq)
  have he : (∑ q ∈ Finset.Icc 2 M, generalFiniteEnergy v M q) =
      27 * ‖finitePotential v M‖^2 := by
    rw [finite_potential_conductor_norm_sq]
    have hterm : (∑ q ∈ Finset.Icc 2 M, generalFiniteEnergy v M q) =
        ∑ q ∈ Finset.Icc 2 M, jordanTwo q * (finiteAmplitude v q M)^2 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact if_pos (Finset.mem_Icc.mp hq).1
    rw [hterm]
    ring
  rwa [he] at h

theorem generalEnergy_hasSum_of_limit (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) (Y : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y)) :
    HasSum (generalEnergy v) (27 * ‖Y‖^2) := by
  exact hasSum_of_nonnegative_rows (generalFiniteEnergy v) (generalEnergy v)
    (fun M => 27 * ‖finitePotential v M‖^2) (27 * ‖Y‖^2)
    (generalFiniteEnergy_nonneg v) (generalEnergy_nonneg v) (generalFiniteEnergy_hasSum v)
    (generalFiniteEnergy_tendsto v hv h0 h1 hs) ((hY.norm.pow 2).const_mul 27)
    (generalFiniteEnergy_le v hv hs)

def ageVector (v : ℕ → ℝ) (k : ℕ) : HaarL2 := (2/3*v k : ℝ) • remainderVector k

theorem ageVector_partial_sum (v : ℕ → ℝ) (h0 : v 0 = 0) (h1 : v 1 = 0) (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), ageVector v k) = finitePotential v M := by
  have he : (∑ k ∈ Finset.Icc 2 M, ageVector v k) =
      ∑ k ∈ Finset.range (M+1), ageVector v k := by
    apply Finset.sum_subset
    · intro k hk
      have := Finset.mem_Icc.mp hk
      simp only [Finset.mem_range]
      omega
    · intro k hk hn
      have hkn := Finset.mem_range.mp hk
      have hk2 : k < 2 := by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega
      interval_cases k <;> simp [ageVector, h0, h1]
  rw [← he]
  simp only [ageVector, finitePotential, mul_smul, Finset.smul_sum]

theorem ageVector_gram_nonneg (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (i j : ℕ) : 0 ≤ inner ℝ (ageVector v i) (ageVector v j) := by
  by_cases hi : i = 0
  · simp [ageVector, hi, h0]
  by_cases hj : j = 0
  · simp [ageVector, hj, h0]
  simp only [ageVector, inner_smul_left, inner_smul_right, conj_trivial]
  exact mul_nonneg (mul_nonneg (by norm_num) (hv j))
    (mul_nonneg (mul_nonneg (by norm_num) (hv i))
      (remainder_inner_nonneg (Nat.pos_of_ne_zero hi) (Nat.pos_of_ne_zero hj)))

theorem general_weights_converge_iff (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) :
    (∃ Y : HaarL2, Tendsto (finitePotential v) atTop (nhds Y)) ↔ Summable (generalEnergy v) := by
  constructor
  · rintro ⟨Y, hY⟩
    exact (generalEnergy_hasSum_of_limit v hv h0 h1 hs Y hY).summable
  · intro he
    have hb : ∀ M, ‖finitePotential v M‖^2 ≤ (∑' q, generalEnergy v q)/27 := by
      intro M
      have hle := (generalFiniteEnergy_hasSum v M).summable.tsum_le_tsum
        (generalFiniteEnergy_le v hv hs M) he
      rw [(generalFiniteEnergy_hasSum v M).tsum_eq] at hle
      linarith
    have hbound : BddAbove (Set.range (fun n => ‖∑ k ∈ Finset.range n, ageVector v k‖^2)) := by
      refine ⟨(∑' q, generalEnergy v q)/27, ?_⟩
      rintro _ ⟨n, rfl⟩
      cases n with
      | zero =>
          change ‖∑ k ∈ Finset.range 0, ageVector v k‖^2 ≤ _
          simp only [Finset.range_zero, Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0)]
          exact div_nonneg (tsum_nonneg (generalEnergy_nonneg v)) (by norm_num)
      | succ M =>
          change ‖∑ k ∈ Finset.range (M+1), ageVector v k‖^2 ≤ _
          rw [ageVector_partial_sum v h0 h1]
          exact hb M
    obtain ⟨Y, hY⟩ := (positive_gram_converges_iff_bounded (ageVector v)
      (ageVector_gram_nonneg v hv h0)).mpr hbound
    refine ⟨Y, ?_⟩
    simpa only [Function.comp_def, ageVector_partial_sum v h0 h1] using
      hY.comp (tendsto_add_atTop_nat 1)

end NField.Alignment.CollisionGeneralWeightCriterion
