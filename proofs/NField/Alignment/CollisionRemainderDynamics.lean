/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.GcdLcmCapacity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Weighted remainder dynamics

The actual coprime harmonic weights and finite centered ages. All identities
below hold for arbitrary natural resolutions or cutoffs. This module does
not construct Haar measure on the profinite completion or prove the
infinite-potential, spectral-tail, or concentration theorems.
-/

namespace NField.Alignment.CollisionRemainderDynamics

open scoped BigOperators
open NField.Alignment.SecondaryCapacityLedger

noncomputable def collisionWeight (k : ℕ) : ℝ :=
  reducedHarmonicStar k / (k : ℝ) ^ 2

noncomputable def centeredRemainder (k n : ℕ) : ℝ :=
  ((n % k : ℕ) : ℝ) - ((k : ℝ) - 1) / 2

noncomputable def finiteAge (v : ℕ → ℝ) (M n : ℕ) : ℝ :=
  (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * centeredRemainder k n

noncomputable def stationaryAge (v : ℕ → ℝ) (M : ℕ) : ℝ :=
  (1 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * ((k : ℝ) - 1)

theorem collisionWeight_nonneg (k : ℕ) : 0 ≤ collisionWeight k := by
  unfold collisionWeight reducedHarmonicStar
  positivity

theorem collisionWeight_pos {k : ℕ} (hk : 2 ≤ k) : 0 < collisionWeight k := by
  unfold collisionWeight reducedHarmonicStar
  apply div_pos
  · apply Finset.sum_pos'
    · intro a ha
      positivity
    · refine ⟨1, ?_, by norm_num⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩, Nat.coprime_one_left k⟩
  · positivity

theorem collisionWeight_two : collisionWeight 2 = 1 / 4 := by
  unfold collisionWeight reducedHarmonicStar
  rw [show Finset.Ico 1 2 = {1} from by decide]
  norm_num [Finset.sum_filter, Nat.Coprime]

theorem collisionWeight_three : collisionWeight 3 = 1 / 6 := by
  unfold collisionWeight reducedHarmonicStar
  rw [show Finset.Ico 1 3 = {1, 2} from by decide]
  norm_num [Finset.sum_filter, Nat.Coprime]

theorem collisionWeight_four : collisionWeight 4 = 1 / 12 := by
  unfold collisionWeight reducedHarmonicStar
  rw [show Finset.Ico 1 4 = {1, 2, 3} from by decide]
  norm_num [Finset.sum_filter, Nat.Coprime]

/-- This is the actual positive mass limit, not a normalization hypothesis. -/
theorem collision_mass_limit :
    Filter.Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, collisionWeight k)
      Filter.atTop (nhds 1) := by
  simpa only [collisionWeight, ← reducedEulerPartialMass_eq_pairWeight_sum,
    reducedEulerPartialMass] using coprime_euler_sum

theorem remainder_step {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (((n + 1) % k : ℕ) : ℝ) - ((n % k : ℕ) : ℝ) =
      1 - if k ∣ n + 1 then (k : ℝ) else 0 := by
  have hr := Nat.mod_lt n hk
  have hs : (n + 1) % k = (n % k + 1) % k := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases ht : n % k + 1 < k
  · have he := hs.trans (Nat.mod_eq_of_lt ht)
    have hn : ¬k ∣ n + 1 := by
      intro h
      have hz := Nat.mod_eq_zero_of_dvd h
      omega
    rw [he, if_neg hn]
    push_cast
    ring
  · have he : n % k + 1 = k := by omega
    have hz : (n + 1) % k = 0 := by rw [hs, he, Nat.mod_self]
    have h := Nat.dvd_of_mod_eq_zero hz
    rw [hz, if_pos h]
    have heR := congrArg (fun j : ℕ => (j : ℝ)) he
    push_cast at heR ⊢
    linarith

theorem centered_remainder_step {k : ℕ} (hk : 0 < k) (n : ℕ) :
    centeredRemainder k (n + 1) - centeredRemainder k n =
      1 - if k ∣ n + 1 then (k : ℝ) else 0 := by
  have h := remainder_step hk n
  unfold centeredRemainder
  linarith

theorem finite_age_step (v : ℕ → ℝ) (M n : ℕ) :
    finiteAge v M (n + 1) - finiteAge v M n =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M,
        v k * (1 - if k ∣ n + 1 then (k : ℝ) else 0) := by
  unfold finiteAge
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_sub, centered_remainder_step (by have := (Finset.mem_Icc.mp hk).1; omega)]

theorem finite_age_block (v : ℕ → ℝ) (M n H : ℕ) :
    (∑ j ∈ Finset.range H,
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M,
        v k * (1 - if k ∣ n + j + 1 then (k : ℝ) else 0)) =
      finiteAge v M (n + H) - finiteAge v M n := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ, ih, ← finite_age_step]
      simp only [Nat.add_assoc]
      ring

theorem finite_age_zero (v : ℕ → ℝ) (M : ℕ) :
    finiteAge v M 0 = -stationaryAge v M := by
  unfold finiteAge stationaryAge centeredRemainder
  simp only [Nat.zero_mod, Nat.cast_zero, zero_sub]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem finite_age_gap (v : ℕ → ℝ) (M n : ℕ) :
    finiteAge v M n + stationaryAge v M =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * ((n % k : ℕ) : ℝ) := by
  unfold finiteAge stationaryAge centeredRemainder
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem finite_age_lower (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (M n : ℕ) :
    -stationaryAge v M ≤ finiteAge v M n := by
  have h := finite_age_gap v M n
  have hnon : 0 ≤ (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M,
      v k * ((n % k : ℕ) : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (Nat.cast_nonneg _)
  linarith

theorem finite_age_upper (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (M n : ℕ) :
    finiteAge v M n ≤ stationaryAge v M := by
  unfold finiteAge stationaryAge
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  have hr : (((n % k : ℕ) : ℝ)) ≤ (k : ℝ) - 1 := by
    have h := Nat.mod_lt n hkpos
    have hc : ((n % k + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith
  have hvk := hv k
  unfold centeredRemainder
  nlinarith

theorem finite_age_endpoint_difference (v : ℕ → ℝ) (M n : ℕ) :
    finiteAge v M n - finiteAge v M 0 =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * ((n % k : ℕ) : ℝ) := by
  rw [finite_age_zero, sub_neg_eq_add, finite_age_gap]

theorem finite_age_min_iff (v : ℕ → ℝ) (hv : ∀ k, 2 ≤ k → 0 < v k)
    (M n : ℕ) :
    finiteAge v M n = -stationaryAge v M ↔
      ∀ k ∈ Finset.Icc 2 M, k ∣ n := by
  have hnon : ∀ k ∈ Finset.Icc 2 M, 0 ≤ v k * ((n % k : ℕ) : ℝ) := by
    intro k hk
    exact mul_nonneg (hv k (Finset.mem_Icc.mp hk).1).le (Nat.cast_nonneg _)
  constructor
  · intro h k hk
    have hsum : (∑ k ∈ Finset.Icc 2 M, v k * ((n % k : ℕ) : ℝ)) = 0 := by
      have hg := finite_age_gap v M n
      rw [h] at hg
      linarith
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hsum k hk
    have hn : ((n % k : ℕ) : ℝ) = 0 :=
      (mul_eq_zero.mp ht).resolve_left (ne_of_gt (hv k (Finset.mem_Icc.mp hk).1))
    exact Nat.dvd_of_mod_eq_zero (by exact_mod_cast hn)
  · intro h
    have hs : (∑ k ∈ Finset.Icc 2 M, v k * ((n % k : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Nat.mod_eq_zero_of_dvd (h k hk)]
      simp
    have hg := finite_age_gap v M n
    rw [hs] at hg
    linarith

theorem finite_age_gap_at_one (v : ℕ → ℝ) (M : ℕ) :
    finiteAge v M 1 + stationaryAge v M =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k := by
  rw [finite_age_gap]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.mod_eq_of_lt (by have := (Finset.mem_Icc.mp hk).1; omega)]
  simp

/-- Exact cutoff identity with the actual continuous capacity. -/
theorem moving_cutoff_ledger (N : ℕ) :
    (N : ℝ) - continuousCapacity N =
      finiteAge collisionWeight N N + stationaryAge collisionWeight N +
        (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N := by
  rw [finite_age_gap, exact_continuous_defect_ledger]
  have h : (∑ k ∈ Finset.Icc 2 N, collisionWeight k * ((N % k : ℕ) : ℝ)) =
      fractionalFloorTerm N := by
    unfold collisionWeight fractionalFloorTerm
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h]
  ring

/-- Endpoint correction between a centered age and a midpoint sawtooth row. -/
theorem endpoint_split (k n : ℕ) :
    centeredRemainder k n =
      (if n % k = 0 then 0 else ((n % k : ℕ) : ℝ) - (k : ℝ) / 2) +
        1 / 2 - (if n % k = 0 then (k : ℝ) / 2 else 0) := by
  unfold centeredRemainder
  split_ifs with h <;> simp [h] <;> ring

/-- A finite cycle has mean zero. -/
theorem centered_cycle_sum {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range k, centeredRemainder k n) = 0 := by
  have he : (∑ n ∈ Finset.range k, centeredRemainder k n) =
      (∑ n ∈ Finset.range k, (n : ℝ)) - (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    simp only [centeredRemainder]
    rw [Finset.sum_sub_distrib]
    have hm : (∑ n ∈ Finset.range k, ((n % k : ℕ) : ℝ)) =
        ∑ n ∈ Finset.range k, (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
    rw [hm]
    simp
    ring
  have hs := congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_range_id_mul_two k)
  have hk1 : 1 ≤ k := hk
  push_cast at hs
  rw [Nat.cast_sub hk1] at hs
  norm_num at hs
  rw [he]
  linarith

/-- The elementary square bound used for endpoint compensation. -/
theorem endpoint_square_bound (x y : ℝ) :
    (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

/-- On any finite stationary phase set, endpoint differences have energy at
most four times the potential energy, independently of the chosen shift. -/
theorem stationary_endpoint_energy {ι : Type*} [Fintype ι]
    (Y : ι → ℝ) (T : Equiv.Perm ι) :
    (∑ x, (Y (T x) - Y x) ^ 2) ≤ 4 * ∑ x, Y x ^ 2 := by
  calc
    _ ≤ ∑ x, (2 * Y (T x) ^ 2 + 2 * Y x ^ 2) :=
      Finset.sum_le_sum fun x _ => endpoint_square_bound _ _
    _ = 2 * (∑ x, Y (T x) ^ 2) + 2 * ∑ x, Y x ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 4 * ∑ x, Y x ^ 2 := by
      rw [Equiv.sum_comp T (fun x => Y x ^ 2)]
      ring

end NField.Alignment.CollisionRemainderDynamics
