/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBoxRows

/-! # Complete frequency-box summation with the original harmonic lifts -/

noncomputable section

namespace NField.Alignment.CommonResetBoxSummation

open scoped BigOperators
open CommonResetBoxRows CommonResetBandCosts CommonResetRootSums CommonResetSmallConductors
open CommonResetDivisorFibers CommonResetBandWeighted

def rootCubeMass : ℝ := ∑' n : ℕ, rootCube n
def harmonicLiftMass : ℝ := ∑' n : ℕ, harmonicLift n

theorem rootCubeMass_nonneg : 0 ≤ rootCubeMass := tsum_nonneg rootCube_nonneg
theorem harmonicLiftMass_nonneg : 0 ≤ harmonicLiftMass := tsum_nonneg harmonicLift_nonneg

theorem reciprocal_sum (Y : ℕ) : (∑ n ∈ Finset.Icc 1 Y, 1/(n : ℝ)) = (harmonic Y : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Title: `The two finite frequency directions cost the square root of the box and a convergent constant`. -/
theorem row_rectangle_bound {p m V J : ℕ} (hm : 1 ≤ m) (hV : V ≤ p) (hJ : J ≤ p) :
    (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, rowCost p m v j) ≤
      ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
        (4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2) +
      (4*(p : ℝ)*Real.sqrt (p : ℝ)/(m : ℝ))*(harmonic p : ℝ)^2 := by
  have hrootJ := sum_reciprocal_sqrt J
  have hrootV := sum_reciprocal_sqrt V
  have hcubeJ := rootCube_sum_le (Finset.Icc 1 J)
  have hcubeV := rootCube_sum_le (Finset.Icc 1 V)
  have hZ := rootCubeMass_nonneg
  have hHJ := harmonic_nonneg J
  have hHV := harmonic_nonneg V
  have hHP := harmonic_nonneg p
  have hCJ : 0 ≤ ∑ j ∈ Finset.Icc 1 J, rootCube j := Finset.sum_nonneg (fun _ _ => rootCube_nonneg _)
  have hCV : 0 ≤ ∑ v ∈ Finset.Icc 1 V, rootCube v := Finset.sum_nonneg (fun _ _ => rootCube_nonneg _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : ((p : ℝ)*Real.sqrt (p : ℝ))/((m : ℝ)^2*Real.sqrt (m : ℝ)) ≤
      ((p : ℝ)*Real.sqrt (p : ℝ))/((m : ℝ)*Real.sqrt (m : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by nlinarith : (m : ℝ) ≤ (m : ℝ)^2) (Real.sqrt_nonneg _)
  calc
    _ = ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
          (∑ j ∈ Finset.Icc 1 J, 1/Real.sqrt (j : ℝ))*(∑ v ∈ Finset.Icc 1 V, 1/Real.sqrt (v : ℝ)) +
        ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*
          (∑ j ∈ Finset.Icc 1 J, rootCube j)*(∑ v ∈ Finset.Icc 1 V, rootCube v) +
        (4*(p : ℝ)*Real.sqrt (p : ℝ)/(m : ℝ))*(harmonic J : ℝ)*(harmonic V : ℝ) := by
      simp_rw [rowCost, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, reciprocal_sum]
    _ ≤ ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
          (2*Real.sqrt (J : ℝ))*(2*Real.sqrt (V : ℝ)) +
        ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*rootCubeMass*rootCubeMass +
        (4*(p : ℝ)*Real.sqrt (p : ℝ)/(m : ℝ))*(harmonic p : ℝ)*(harmonic p : ℝ) := by
      apply add_le_add (add_le_add ?_ ?_) ?_
      · gcongr
      · exact mul_le_mul (mul_le_mul hden hcubeJ hCJ (by positivity)) hcubeV hCV (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (harmonic_monotone hJ) (by positivity))
          (harmonic_monotone hV) hHV (by positivity)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg J)]; ring

theorem harmonic_weighted_reciprocal (p : ℕ) :
    (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)/(m : ℝ)) ≤ (harmonic p : ℝ)^2 := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 p, (harmonic p : ℝ)/(m : ℝ) := by
      exact Finset.sum_le_sum (fun m hm => div_le_div_of_nonneg_right
        (harmonic_monotone (Finset.mem_Icc.mp hm).2) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      have he := reciprocal_sum p
      simp only [one_div] at he
      rw [he]
      ring

/-- Title: `The exact harmonic band lifts are included in the complete rectangular frequency cost`. -/
theorem harmonic_box_cost {p V J : ℕ} (hV : V ≤ p) (hJ : J ≤ p) :
    (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
      (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, rowCost p m v j)) ≤
      (p : ℝ)*Real.sqrt (p : ℝ)*
        (harmonicLiftMass*(4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)+4*(harmonic p : ℝ)^4) := by
  have hT := harmonicLiftMass_nonneg
  have hZ := rootCubeMass_nonneg
  have hH := harmonic_nonneg p
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
        (((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
          (4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)+
          (4*(p : ℝ)*Real.sqrt (p : ℝ)/(m : ℝ))*(harmonic p : ℝ)^2) := by
      exact Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left
        (row_rectangle_bound (Finset.mem_Icc.mp hm).1 hV hJ) (harmonic_nonneg m))
    _ = (p : ℝ)*Real.sqrt (p : ℝ)*(4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)*
          (∑ m ∈ Finset.Icc 1 p, harmonicLift m) +
        (4*(p : ℝ)*Real.sqrt (p : ℝ))*(harmonic p : ℝ)^2*
          (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)/(m : ℝ)) := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      unfold harmonicLift
      ring
    _ ≤ (p : ℝ)*Real.sqrt (p : ℝ)*(4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)*harmonicLiftMass +
        (4*(p : ℝ)*Real.sqrt (p : ℝ))*(harmonic p : ℝ)^2*(harmonic p : ℝ)^2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (harmonicLift_sum_le _) (by positivity))
        (mul_le_mul_of_nonneg_left (harmonic_weighted_reciprocal p) (by positivity))
    _ = _ := by ring

end NField.Alignment.CommonResetBoxSummation
