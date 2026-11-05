/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeEnclosure

/-!
# Finite rational bounds for bounded collision-weighted series

The actual omitted unit mass controls every bounded coefficient sequence.
Summability and containment are conclusions, with no numerical approximation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionWeightedEnclosure

open scoped BigOperators Classical
open Filter CollisionRemainderDynamics CollisionMassReadout
open CollisionIntegerSingularity CollisionAmplitudeEnclosure

def weightedPrefix (f : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 M, collisionWeight k * f k

def weightedRemainder (f : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑' j : ℕ, collisionWeight (j+(M+1)) * f (j+(M+1))

theorem bounded_weighted_summable {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) : Summable (fun k => collisionWeight k * f k) := by
  apply Summable.of_norm_bounded (collisionWeight_summable.mul_right B)
  intro k
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionWeight_nonneg k)]
  exact mul_le_mul_of_nonneg_left (hf k) (collisionWeight_nonneg k)

theorem weightedRemainder_summable {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) (M : ℕ) :
    Summable (fun j => collisionWeight (j+(M+1)) * f (j+(M+1))) :=
  (bounded_weighted_summable hf).comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem weighted_cutoff_split {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) (M : ℕ) :
    (∑' k, collisionWeight k * f k) = weightedPrefix f M + weightedRemainder f M := by
  have h := (bounded_weighted_summable hf).sum_add_tsum_nat_add (M+1)
  rw [sum_range_zero_one _ (by simp) (by simp)] at h
  exact h.symm

theorem weightedRemainder_abs_bound {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) (M : ℕ) :
    |weightedRemainder f M| ≤ B * tailMass M := by
  have hs := weightedRemainder_summable hf M
  have hmajor := (collisionWeight_summable.comp_injective
    (fun _ _ h => Nat.add_right_cancel h : Function.Injective (fun j : ℕ => j+(M+1)))).mul_right B
  have h := hs.norm.tsum_le_tsum (fun j => ?_) hmajor
  · have hn := norm_tsum_le_tsum_norm hs.norm
    rw [tsum_mul_right] at h
    change (∑' j, ‖collisionWeight (j+(M+1))*f (j+(M+1))‖) ≤ tailMass M*B at h
    simpa only [weightedRemainder,Real.norm_eq_abs,mul_comm B] using hn.trans h
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hf _) (collisionWeight_nonneg _)

theorem weightedRemainder_nonneg {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (M : ℕ) :
    0 ≤ weightedRemainder f M :=
  tsum_nonneg (fun _ => mul_nonneg (collisionWeight_nonneg _) (hf _))

theorem weightedPrefix_nonneg {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (M : ℕ) :
    0 ≤ weightedPrefix f M :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (collisionWeight_nonneg k) (hf k))

theorem weighted_series_enclosure {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) (M : ℕ) :
    (∑' k, collisionWeight k*f k) ∈
      Set.Icc (weightedPrefix f M-B*tailMass M) (weightedPrefix f M+B*tailMass M) := by
  rw [weighted_cutoff_split hf M]
  have h := abs_le.mp (weightedRemainder_abs_bound hf M)
  constructor <;> linarith

theorem positive_weighted_series_enclosure {f : ℕ → ℝ} {B : ℝ}
    (h0 : ∀ k, 0 ≤ f k) (hB : ∀ k, f k ≤ B) (M : ℕ) :
    (∑' k, collisionWeight k*f k) ∈
      Set.Icc (weightedPrefix f M) (weightedPrefix f M+B*tailMass M) := by
  have hf : ∀ k, |f k| ≤ B := by intro k; rw [abs_of_nonneg (h0 k)]; exact hB k
  have h := weighted_series_enclosure hf M
  refine ⟨?_,h.2⟩
  rw [weighted_cutoff_split hf M]
  exact le_add_of_nonneg_right (weightedRemainder_nonneg h0 M)

theorem weightedPrefix_tendsto {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ k, |f k| ≤ B) :
    Tendsto (weightedPrefix f) atTop (nhds (∑' k, collisionWeight k*f k)) := by
  have h := (bounded_weighted_summable hf).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have he (M : ℕ) : (∑ k ∈ Finset.range (M+1), collisionWeight k*f k)=weightedPrefix f M :=
    sum_range_zero_one (fun k => collisionWeight k*f k) (by simp) (by simp) M
  simpa only [Function.comp_def,he] using h

theorem weighted_enclosure_radius_tendsto (B : ℝ) :
    Tendsto (fun M => B*tailMass M) atTop (nhds 0) := by
  simpa only [mul_zero] using tailMass_tendsto_zero.const_mul B

end NField.Alignment.CollisionWeightedEnclosure
