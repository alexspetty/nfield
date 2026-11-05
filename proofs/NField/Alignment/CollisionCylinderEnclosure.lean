/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionWeightedEnclosure
import NField.Alignment.CollisionPositionStability

/-!
# Exact finite enclosures for actual Haar cylinder means

The finite rational centers use the actual period weights. The radius is
one third of L-1 times the omitted unit mass. The fixed-cylinder width
tends to zero, with no assignment of integer values to the L2 potential.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCylinderEnclosure

open scoped BigOperators Classical
open Filter CollisionRemainderDynamics CollisionCylinderMeans CollisionPositionStability
open CollisionIntegerSingularity CollisionWeightedEnclosure

def alignmentCoefficient (L k : ℕ) : ℝ := ((k.gcd L : ℝ)-1)/3
def meanCoefficient (L a k : ℕ) : ℝ := (2/3)*centeredRemainder (k.gcd L) a
def gapCoefficient (L a k : ℕ) : ℝ := (2/3)*((a % k.gcd L : ℕ) : ℝ)
def finiteAlignment (L M : ℕ) : ℝ := weightedPrefix (alignmentCoefficient L) M
def finiteCylinderMean (L a M : ℕ) : ℝ := weightedPrefix (meanCoefficient L a) M
def finiteCylinderGap (L a M : ℕ) : ℝ := weightedPrefix (gapCoefficient L a) M
def cylinderRadius (L M : ℕ) : ℝ := ((L : ℝ)-1)/3*tailMass M

theorem alignmentCoefficient_bounds {L : ℕ} (hL : 0 < L) (k : ℕ) :
    0 ≤ alignmentCoefficient L k ∧ alignmentCoefficient L k ≤ ((L : ℝ)-1)/3 := by
  have hd1 : (1 : ℝ) ≤ k.gcd L := by exact_mod_cast Nat.gcd_pos_of_pos_right k hL
  have hdL : (k.gcd L : ℝ) ≤ L := by exact_mod_cast Nat.gcd_le_right k hL
  unfold alignmentCoefficient
  constructor <;> linarith

theorem gapCoefficient_bounds {L : ℕ} (hL : 0 < L) (a k : ℕ) :
    0 ≤ gapCoefficient L a k ∧ gapCoefficient L a k ≤ 2*alignmentCoefficient L k := by
  have hr0 : (0 : ℝ) ≤ (a % k.gcd L : ℕ) := Nat.cast_nonneg _
  have hr1 : ((a % k.gcd L : ℕ) : ℝ)+1 ≤ k.gcd L := by
    exact_mod_cast Nat.mod_lt a (Nat.gcd_pos_of_pos_right k hL)
  unfold gapCoefficient alignmentCoefficient
  constructor <;> linarith

theorem meanCoefficient_abs_bound {L : ℕ} (hL : 0 < L) (a k : ℕ) :
    |meanCoefficient L a k| ≤ ((L : ℝ)-1)/3 := by
  have hdL : (k.gcd L : ℝ) ≤ L := by exact_mod_cast Nat.gcd_le_right k hL
  have hg := gapCoefficient_bounds hL a k
  have hc := alignmentCoefficient_bounds hL k
  unfold meanCoefficient centeredRemainder gapCoefficient alignmentCoefficient at *
  rw [abs_le]
  constructor <;> linarith

theorem alignmentConstant_weighted {L : ℕ} (_hL : 0 < L) :
    alignmentConstant L = ∑' k, collisionWeight k*alignmentCoefficient L k := by
  rw [alignmentConstant,← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold alignmentCoefficient
  ring

theorem cylinderMean_weighted {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a = ∑' k, collisionWeight k*meanCoefficient L a k := by
  rw [cylinderMean_series hL,← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold meanCoefficient
  ring

theorem cylinderGap_weighted {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a+alignmentConstant L = ∑' k, collisionWeight k*gapCoefficient L a k := by
  rw [cylinderMean_gap hL,← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold gapCoefficient ageTerm
  ring

theorem finiteAlignment_formula (L M : ℕ) :
    finiteAlignment L M = (1/3)*∑ k ∈ Finset.Icc 2 M,
      collisionWeight k*((k.gcd L : ℝ)-1) := by
  rw [finiteAlignment,weightedPrefix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold alignmentCoefficient
  ring

theorem finiteCylinderMean_formula (L a M : ℕ) :
    finiteCylinderMean L a M = (2/3)*∑ k ∈ Finset.Icc 2 M,
      collisionWeight k*centeredRemainder (k.gcd L) a := by
  rw [finiteCylinderMean,weightedPrefix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold meanCoefficient
  ring

theorem finiteCylinderGap_eq (L a M : ℕ) :
    finiteCylinderGap L a M=finiteCylinderMean L a M+finiteAlignment L M := by
  unfold finiteCylinderGap finiteCylinderMean finiteAlignment weightedPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold gapCoefficient meanCoefficient alignmentCoefficient centeredRemainder
  ring

theorem finiteAlignment_nonneg {L : ℕ} (hL : 0 < L) (M : ℕ) :
    0 ≤ finiteAlignment L M :=
  weightedPrefix_nonneg (fun k => (alignmentCoefficient_bounds hL k).1) M

theorem finiteAlignment_pos {L M : ℕ} (hL : 2 ≤ L) (hM : L ≤ M) :
    0 < finiteAlignment L M := by
  unfold finiteAlignment weightedPrefix
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (collisionWeight_nonneg k) (alignmentCoefficient_bounds (by omega) k).1
  · refine ⟨L,Finset.mem_Icc.mpr ⟨hL,hM⟩,?_⟩
    apply mul_pos (collisionWeight_pos hL)
    unfold alignmentCoefficient
    rw [Nat.gcd_self]
    have h : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith

theorem cylinderRadius_nonneg {L : ℕ} (hL : 0 < L) (M : ℕ) :
    0 ≤ cylinderRadius L M := by
  have h : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact mul_nonneg (by linarith) (tailMass_nonneg M)

theorem alignment_enclosure {L : ℕ} (hL : 0 < L) (M : ℕ) :
    alignmentConstant L ∈ Set.Icc (finiteAlignment L M) (finiteAlignment L M+cylinderRadius L M) := by
  rw [alignmentConstant_weighted hL]
  exact positive_weighted_series_enclosure
    (fun k => (alignmentCoefficient_bounds hL k).1)
    (fun k => (alignmentCoefficient_bounds hL k).2) M

theorem cylinderMean_enclosure {L : ℕ} (hL : 0 < L) (a M : ℕ) :
    cylinderMean L a ∈ Set.Icc (finiteCylinderMean L a M-cylinderRadius L M)
      (finiteCylinderMean L a M+cylinderRadius L M) := by
  rw [cylinderMean_weighted hL]
  exact weighted_series_enclosure (meanCoefficient_abs_bound hL a) M

theorem cylinderGap_enclosure {L : ℕ} (hL : 0 < L) (a M : ℕ) :
    cylinderMean L a+alignmentConstant L ∈ Set.Icc (finiteCylinderGap L a M)
      (finiteCylinderGap L a M+2*cylinderRadius L M) := by
  have h := positive_weighted_series_enclosure
    (fun k => (gapCoefficient_bounds hL a k).1)
    (fun k => (gapCoefficient_bounds hL a k).2.trans
      (mul_le_mul_of_nonneg_left (alignmentCoefficient_bounds hL k).2 (by norm_num : (0 : ℝ) ≤ 2))) M
  rw [← cylinderGap_weighted hL a] at h
  refine ⟨h.1,?_⟩
  convert! h.2 using 1
  unfold finiteCylinderGap cylinderRadius
  ring

theorem finiteCylinderGap_bounds {L : ℕ} (hL : 0 < L) (a M : ℕ) :
    0 ≤ finiteCylinderGap L a M ∧ finiteCylinderGap L a M ≤ 2*finiteAlignment L M := by
  refine ⟨weightedPrefix_nonneg (fun k => (gapCoefficient_bounds hL a k).1) M,?_⟩
  unfold finiteCylinderGap finiteAlignment weightedPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  nlinarith [mul_le_mul_of_nonneg_left (gapCoefficient_bounds hL a k).2 (collisionWeight_nonneg k)]

theorem cylinderRadius_tendsto (L : ℕ) :
    Tendsto (cylinderRadius L) atTop (nhds 0) :=
  weighted_enclosure_radius_tendsto _

theorem finiteAlignment_tendsto {L : ℕ} (hL : 0 < L) :
    Tendsto (finiteAlignment L) atTop (nhds (alignmentConstant L)) := by
  rw [alignmentConstant_weighted hL]
  exact weightedPrefix_tendsto (fun k => by
    rw [abs_of_nonneg (alignmentCoefficient_bounds hL k).1]
    exact (alignmentCoefficient_bounds hL k).2)

theorem finiteCylinderMean_tendsto {L : ℕ} (hL : 0 < L) (a : ℕ) :
    Tendsto (finiteCylinderMean L a) atTop (nhds (cylinderMean L a)) := by
  rw [cylinderMean_weighted hL]
  exact weightedPrefix_tendsto (meanCoefficient_abs_bound hL a)

end NField.Alignment.CollisionCylinderEnclosure
