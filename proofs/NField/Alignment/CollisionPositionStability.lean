/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderMeans

/-!
# Position weights and stability on actual Haar cylinders

The weights form a probability on periods sharing a nontrivial divisor
with the cylinder. The cylinder gap is its mean relative residue.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositionStability

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionPotentialConvergence CollisionCylinderMeans

def positionWeight (L k : ℕ) : ℝ :=
  if 1 < k.gcd L then collisionWeight k*((k.gcd L : ℝ)-1)/(3*alignmentConstant L) else 0

def relativePosition (L a k : ℕ) : ℝ :=
  ((a % k.gcd L : ℕ) : ℝ)/((k.gcd L : ℝ)-1)

def positionExceedanceMass (L a : ℕ) (δ : ℝ) : ℝ :=
  ∑' k : ℕ, if δ < relativePosition L a k then positionWeight L k else 0

theorem alignmentConstant_pos {L : ℕ} (hL : 2 ≤ L) : 0 < alignmentConstant L := by
  have hLp : 0 < L := by omega
  have hn : ∀ k, 0 ≤ collisionWeight k*((k.gcd L : ℝ)-1) := by
    intro k
    apply mul_nonneg (collisionWeight_nonneg k)
    have h : (1 : ℝ) ≤ k.gcd L := by exact_mod_cast Nat.gcd_pos_of_pos_right k hLp
    linarith
  have h := (alignment_series_summable hLp).le_tsum L (fun k _ => hn k)
  simp only [Nat.gcd_self] at h
  have hp : 0 < collisionWeight L*((L : ℝ)-1) := by
    apply mul_pos (collisionWeight_pos hL)
    have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  unfold alignmentConstant
  exact mul_pos (by norm_num) (hp.trans_le h)

theorem positionWeight_eq {L : ℕ} (hL : 0 < L) (k : ℕ) :
    positionWeight L k=collisionWeight k*((k.gcd L : ℝ)-1)/(3*alignmentConstant L) := by
  unfold positionWeight
  split_ifs with hk
  · rfl
  · have hd : k.gcd L=1 := by have := Nat.gcd_pos_of_pos_right k hL; omega
    simp only [hd,Nat.cast_one,sub_self,mul_zero,zero_div]

theorem positionWeight_nonneg {L : ℕ} (hL : 2 ≤ L) (k : ℕ) : 0 ≤ positionWeight L k := by
  rw [positionWeight_eq (by omega : 0 < L)]
  apply div_nonneg _ (by positivity [alignmentConstant_pos hL])
  apply mul_nonneg (collisionWeight_nonneg k)
  have h : (1 : ℝ) ≤ k.gcd L := by
    exact_mod_cast Nat.gcd_pos_of_pos_right k (by omega : 0 < L)
  linarith

theorem positionWeight_summable {L : ℕ} (hL : 2 ≤ L) : Summable (positionWeight L) := by
  have h := (alignment_series_summable (by omega : 0 < L)).div_const (3*alignmentConstant L)
  apply h.congr
  intro k
  exact (positionWeight_eq (by omega : 0 < L) k).symm

theorem positionWeight_tsum {L : ℕ} (hL : 2 ≤ L) : (∑' k, positionWeight L k)=1 := by
  have he : (fun k => positionWeight L k)=
      (fun k => collisionWeight k*((k.gcd L : ℝ)-1)/(3*alignmentConstant L)) :=
    funext (positionWeight_eq (by omega : 0 < L))
  rw [he,tsum_div_const]
  have hs : (∑' k, collisionWeight k*((k.gcd L : ℝ)-1))=3*alignmentConstant L := by
    unfold alignmentConstant
    ring
  rw [hs]
  exact div_self (by positivity [alignmentConstant_pos hL])

theorem relativePosition_nonneg {L : ℕ} (hL : 0 < L) (a k : ℕ) :
    0 ≤ relativePosition L a k := by
  unfold relativePosition
  apply div_nonneg (Nat.cast_nonneg _)
  have h : (1 : ℝ) ≤ k.gcd L := by exact_mod_cast Nat.gcd_pos_of_pos_right k hL
  linarith

theorem relativePosition_le_one {L : ℕ} (hL : 0 < L) (a k : ℕ) :
    relativePosition L a k ≤ 1 := by
  by_cases hd : k.gcd L=1
  · simp [relativePosition,hd]
  have hd2 : 2 ≤ k.gcd L := by have := Nat.gcd_pos_of_pos_right k hL; omega
  have hdR : (2 : ℝ) ≤ k.gcd L := by exact_mod_cast hd2
  unfold relativePosition
  apply (div_le_one (by linarith : 0 < (k.gcd L : ℝ)-1)).mpr
  have hr : ((a % k.gcd L : ℕ) : ℝ)+1 ≤ k.gcd L := by
    exact_mod_cast Nat.mod_lt a (Nat.gcd_pos_of_pos_right k hL)
  linarith

theorem position_product_eq {L : ℕ} (hL : 2 ≤ L) (a k : ℕ) :
    positionWeight L k*relativePosition L a k=ageTerm L a k/(3*alignmentConstant L) := by
  rw [positionWeight_eq (by omega : 0 < L)]
  by_cases hd : k.gcd L=1
  · simp only [relativePosition,ageTerm,hd,Nat.mod_one,Nat.cast_one,Nat.cast_zero,
      sub_self,mul_zero,zero_div]
  have hd2 : 2 ≤ k.gcd L := by
    have := Nat.gcd_pos_of_pos_right k (by omega : 0 < L)
    omega
  have hdR : (k.gcd L : ℝ)-1≠0 := by
    have h : (2 : ℝ) ≤ k.gcd L := by exact_mod_cast hd2
    linarith
  unfold relativePosition ageTerm
  field_simp

theorem position_product_summable {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    Summable (fun k => positionWeight L k*relativePosition L a k) := by
  have h := (ageTerm_summable (by omega : 0 < L) a).div_const (3*alignmentConstant L)
  apply h.congr
  intro k
  exact (position_product_eq hL a k).symm

theorem normalized_cylinder_position {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L)=
      ∑' k, positionWeight L k*relativePosition L a k := by
  simp only [position_product_eq hL,tsum_div_const]
  rw [cylinderMean_gap (by omega : 0 < L)]
  field_simp

theorem positionExceedance_summable {L : ℕ} (hL : 2 ≤ L) (a : ℕ) (δ : ℝ) :
    Summable (fun k : ℕ => if δ < relativePosition L a k then positionWeight L k else 0) := by
  apply ((positionWeight_summable hL).indicator {k : ℕ | δ < relativePosition L a k}).congr
  intro k
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem position_markov_bound {L : ℕ} (hL : 2 ≤ L) (a : ℕ) (δ : ℝ) :
    δ*positionExceedanceMass L a δ ≤
      (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L) := by
  have hbound : ∀ k : ℕ,
      δ*(if δ < relativePosition L a k then positionWeight L k else 0) ≤
        positionWeight L k*relativePosition L a k := by
    intro k
    split_ifs with hk
    · have h := mul_le_mul_of_nonneg_left hk.le (positionWeight_nonneg hL k)
      simpa only [mul_comm δ] using h
    · rw [mul_zero]
      exact mul_nonneg (positionWeight_nonneg hL k)
        (relativePosition_nonneg (by omega : 0 < L) a k)
  have h := ((positionExceedance_summable hL a δ).mul_left δ).tsum_le_tsum hbound
    (position_product_summable hL a)
  rw [tsum_mul_left,← normalized_cylinder_position hL a] at h
  exact h

theorem position_stability {L : ℕ} (hL : 2 ≤ L) (a : ℕ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgap : cylinderMean L a+alignmentConstant L ≤ ε*alignmentConstant L) :
    positionExceedanceMass L a δ ≤ ε/(2*δ) := by
  have hC := alignmentConstant_pos hL
  have hmean : (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L) ≤ ε/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*alignmentConstant L)).mpr
    nlinarith
  have hb := position_markov_bound hL a δ
  apply (le_div_iff₀ (by positivity : 0 < 2*δ)).mpr
  nlinarith

end NField.Alignment.CollisionPositionStability
