/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderEnclosure

/-!
# Certified relative-position probabilities

Positive finite alignment permits rational interval division. Every bound
refers to the full normalized cylinder probability, including the omitted
period mass. The finite cutoff does not redefine that probability.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositionEnclosure

open scoped BigOperators Classical
open Filter CollisionRemainderDynamics CollisionCylinderMeans CollisionPositionStability
open CollisionIntegerSingularity CollisionWeightedEnclosure CollisionCylinderEnclosure

def eventCoefficient (L a : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if δ < relativePosition L a k then alignmentCoefficient L k else 0

def finitePositionEvent (L a : ℕ) (δ : ℝ) (M : ℕ) : ℝ :=
  weightedPrefix (eventCoefficient L a δ) M

def positionNumerator (L k : ℕ) : ℝ := collisionWeight k*alignmentCoefficient L k

def omittedPositionMass (L M : ℕ) : ℝ := ∑' j, positionWeight L (j+(M+1))

theorem positive_ratio_enclosure {x lo hi C Clo Cup : ℝ}
    (hlo : 0 ≤ lo) (hx : x ∈ Set.Icc lo hi) (hClo : 0 < Clo)
    (hC : C ∈ Set.Icc Clo Cup) (hxC : x ≤ C) :
    x/C ∈ Set.Icc (lo/Cup) (min 1 (hi/Clo)) := by
  have hCp : 0 < C := hClo.trans_le hC.1
  have hx0 := hlo.trans hx.1
  refine ⟨div_le_div₀ hx0 hx.1 hCp hC.2,le_min ?_ ?_⟩
  · exact (div_le_one hCp).mpr hxC
  · exact div_le_div₀ (hx0.trans hx.2) hx.2 hClo hC.1

theorem eventCoefficient_bounds {L : ℕ} (hL : 0 < L) (a : ℕ) (δ : ℝ) (k : ℕ) :
    0 ≤ eventCoefficient L a δ k ∧ eventCoefficient L a δ k ≤ alignmentCoefficient L k := by
  unfold eventCoefficient
  split_ifs
  · exact ⟨(alignmentCoefficient_bounds hL k).1,le_rfl⟩
  · exact ⟨le_rfl,(alignmentCoefficient_bounds hL k).1⟩

theorem event_series_enclosure {L : ℕ} (hL : 0 < L) (a M : ℕ) (δ : ℝ) :
    (∑' k, collisionWeight k*eventCoefficient L a δ k) ∈
      Set.Icc (finitePositionEvent L a δ M)
        (finitePositionEvent L a δ M+cylinderRadius L M) :=
  positive_weighted_series_enclosure
    (fun k => (eventCoefficient_bounds hL a δ k).1)
    (fun k => (eventCoefficient_bounds hL a δ k).2.trans (alignmentCoefficient_bounds hL k).2) M

theorem event_series_le_alignment {L : ℕ} (hL : 0 < L) (a : ℕ) (δ : ℝ) :
    (∑' k, collisionWeight k*eventCoefficient L a δ k) ≤ alignmentConstant L := by
  rw [alignmentConstant_weighted hL]
  have he (k : ℕ) : |eventCoefficient L a δ k| ≤ ((L : ℝ)-1)/3 := by
    rw [abs_of_nonneg (eventCoefficient_bounds hL a δ k).1]
    exact (eventCoefficient_bounds hL a δ k).2.trans (alignmentCoefficient_bounds hL k).2
  have hc (k : ℕ) : |alignmentCoefficient L k| ≤ ((L : ℝ)-1)/3 := by
    rw [abs_of_nonneg (alignmentCoefficient_bounds hL k).1]
    exact (alignmentCoefficient_bounds hL k).2
  exact (bounded_weighted_summable he).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (eventCoefficient_bounds hL a δ k).2 (collisionWeight_nonneg k))
    (bounded_weighted_summable hc)

theorem positionWeight_numerator {L : ℕ} (hL : 0 < L) (k : ℕ) :
    positionWeight L k=positionNumerator L k/alignmentConstant L := by
  rw [positionWeight_eq hL]
  unfold positionNumerator alignmentCoefficient
  ring

theorem positionExceedance_numerator {L : ℕ} (hL : 0 < L) (a : ℕ) (δ : ℝ) :
    positionExceedanceMass L a δ=
      (∑' k, collisionWeight k*eventCoefficient L a δ k)/alignmentConstant L := by
  have he (k : ℕ) : (if δ < relativePosition L a k then positionWeight L k else 0)=
      collisionWeight k*eventCoefficient L a δ k/alignmentConstant L := by
    unfold eventCoefficient
    split_ifs
    · exact positionWeight_numerator hL k
    · simp only [mul_zero,zero_div]
  simp only [positionExceedanceMass,he,tsum_div_const]

theorem positionExceedance_enclosure {L M : ℕ} (hL : 2 ≤ L) (hM : L ≤ M) (a : ℕ) (δ : ℝ) :
    positionExceedanceMass L a δ ∈
      Set.Icc (finitePositionEvent L a δ M/(finiteAlignment L M+cylinderRadius L M))
        (min 1 ((finitePositionEvent L a δ M+cylinderRadius L M)/finiteAlignment L M)) := by
  have hLp : 0 < L := by omega
  rw [positionExceedance_numerator hLp]
  exact positive_ratio_enclosure
    (weightedPrefix_nonneg (fun k => (eventCoefficient_bounds hLp a δ k).1) M)
    (event_series_enclosure hLp a M δ) (finiteAlignment_pos hL hM)
    (alignment_enclosure hLp M) (event_series_le_alignment hLp a δ)

theorem normalizedGap_enclosure {L M : ℕ} (hL : 2 ≤ L) (hM : L ≤ M) (a : ℕ) :
    (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L) ∈
      Set.Icc ((finiteCylinderGap L a M/2)/(finiteAlignment L M+cylinderRadius L M))
        (min 1 ((finiteCylinderGap L a M/2+cylinderRadius L M)/finiteAlignment L M)) := by
  have hLp : 0 < L := by omega
  have hg := cylinderGap_enclosure hLp a M
  have hn := finiteCylinderGap_bounds hLp a M
  have hx : (cylinderMean L a+alignmentConstant L)/2 ∈
      Set.Icc (finiteCylinderGap L a M/2) (finiteCylinderGap L a M/2+cylinderRadius L M) := by
    constructor <;> linarith [hg.1,hg.2]
  have hc : (cylinderMean L a+alignmentConstant L)/2 ≤ alignmentConstant L := by
    linarith [cylinderMean_upper hLp a]
  have h := positive_ratio_enclosure (div_nonneg hn.1 (by norm_num)) hx
    (finiteAlignment_pos hL hM) (alignment_enclosure hLp M) hc
  have he : ((cylinderMean L a+alignmentConstant L)/2)/alignmentConstant L=
      (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L) := by ring
  rw [he] at h
  exact h

theorem positionNumerator_nonneg {L : ℕ} (hL : 0 < L) (k : ℕ) :
    0 ≤ positionNumerator L k :=
  mul_nonneg (collisionWeight_nonneg k) (alignmentCoefficient_bounds hL k).1

theorem positionNumerator_le_alignment {L : ℕ} (hL : 0 < L) (k : ℕ) :
    positionNumerator L k ≤ alignmentConstant L := by
  rw [alignmentConstant_weighted hL]
  exact (bounded_weighted_summable (fun j => by
    rw [abs_of_nonneg (alignmentCoefficient_bounds hL j).1]
    exact (alignmentCoefficient_bounds hL j).2)).le_tsum k
      (fun j _ => positionNumerator_nonneg hL j)

theorem positionWeight_enclosure {L M : ℕ} (hL : 2 ≤ L) (hM : L ≤ M) (k : ℕ) :
    positionWeight L k ∈
      Set.Icc (positionNumerator L k/(finiteAlignment L M+cylinderRadius L M))
        (min 1 (positionNumerator L k/finiteAlignment L M)) := by
  have hLp : 0 < L := by omega
  rw [positionWeight_numerator hLp]
  exact positive_ratio_enclosure (positionNumerator_nonneg hLp k) ⟨le_rfl,le_rfl⟩
    (finiteAlignment_pos hL hM) (alignment_enclosure hLp M) (positionNumerator_le_alignment hLp k)

theorem omittedPositionMass_numerator {L : ℕ} (hL : 0 < L) (M : ℕ) :
    omittedPositionMass L M=weightedRemainder (alignmentCoefficient L) M/alignmentConstant L := by
  simp only [omittedPositionMass,positionWeight_numerator hL,positionNumerator,
    weightedRemainder,tsum_div_const]

theorem omittedPositionMass_enclosure {L M : ℕ} (hL : 2 ≤ L) (hM : L ≤ M) :
    omittedPositionMass L M ∈ Set.Icc 0 (min 1 (cylinderRadius L M/finiteAlignment L M)) := by
  have hLp : 0 < L := by omega
  have hf : ∀ k, |alignmentCoefficient L k| ≤ ((L : ℝ)-1)/3 := by
    intro k
    rw [abs_of_nonneg (alignmentCoefficient_bounds hLp k).1]
    exact (alignmentCoefficient_bounds hLp k).2
  have hn := weightedRemainder_nonneg (fun k => (alignmentCoefficient_bounds hLp k).1) M
  have hb := weightedRemainder_abs_bound hf M
  rw [abs_of_nonneg hn] at hb
  have hc : weightedRemainder (alignmentCoefficient L) M ≤ alignmentConstant L := by
    rw [alignmentConstant_weighted hLp,weighted_cutoff_split hf M]
    exact le_add_of_nonneg_left (finiteAlignment_nonneg hLp M)
  have h := positive_ratio_enclosure (le_rfl : (0 : ℝ) ≤ 0) ⟨hn,hb⟩
    (finiteAlignment_pos hL hM) (alignment_enclosure hLp M) hc
  simpa only [zero_div,← omittedPositionMass_numerator hLp M,cylinderRadius] using h

theorem finitePositionEvent_tendsto {L : ℕ} (hL : 0 < L) (a : ℕ) (δ : ℝ) :
    Tendsto (finitePositionEvent L a δ) atTop
      (nhds (∑' k, collisionWeight k*eventCoefficient L a δ k)) :=
  weightedPrefix_tendsto (fun k => by
    rw [abs_of_nonneg (eventCoefficient_bounds hL a δ k).1]
    exact (eventCoefficient_bounds hL a δ k).2.trans (alignmentCoefficient_bounds hL k).2)

theorem ratio_enclosure_limits {N D R S : ℕ → ℝ} {x C : ℝ}
    (hN : Tendsto N atTop (nhds x)) (hD : Tendsto D atTop (nhds C))
    (hR : Tendsto R atTop (nhds 0)) (hS : Tendsto S atTop (nhds 0))
    (hC : 0 < C) (hx : x/C ≤ 1) :
    Tendsto (fun M => N M/(D M+R M)) atTop (nhds (x/C)) ∧
    Tendsto (fun M => min 1 ((N M+S M)/D M)) atTop (nhds (x/C)) ∧
    Tendsto (fun M => min 1 ((N M+S M)/D M)-N M/(D M+R M)) atTop (nhds 0) := by
  have hl := hN.div (hD.add hR) (by simpa only [add_zero] using hC.ne')
  simp only [add_zero] at hl
  have hu := (tendsto_const_nhds (x := (1 : ℝ))).min ((hN.add hS).div hD hC.ne')
  simp only [add_zero,min_eq_right hx] at hu
  refine ⟨hl,hu,?_⟩
  have hw := hu.sub hl
  simp only [sub_self] at hw
  convert! hw using 1

theorem positionExceedance_enclosure_limits {L : ℕ} (hL : 2 ≤ L) (a : ℕ) (δ : ℝ) :
    Tendsto (fun M => finitePositionEvent L a δ M/(finiteAlignment L M+cylinderRadius L M))
      atTop (nhds (positionExceedanceMass L a δ)) ∧
    Tendsto (fun M => min 1 ((finitePositionEvent L a δ M+cylinderRadius L M)/finiteAlignment L M))
      atTop (nhds (positionExceedanceMass L a δ)) ∧
    Tendsto (fun M => min 1 ((finitePositionEvent L a δ M+cylinderRadius L M)/finiteAlignment L M)-
      finitePositionEvent L a δ M/(finiteAlignment L M+cylinderRadius L M)) atTop (nhds 0) := by
  have hLp : 0 < L := by omega
  have h := ratio_enclosure_limits (finitePositionEvent_tendsto hLp a δ)
    (finiteAlignment_tendsto hLp) (cylinderRadius_tendsto L) (cylinderRadius_tendsto L)
    (alignmentConstant_pos hL) ((div_le_one (alignmentConstant_pos hL)).mpr
      (event_series_le_alignment hLp a δ))
  simpa only [← positionExceedance_numerator hLp a δ] using h

theorem normalizedGap_enclosure_limits {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    Tendsto (fun M => (finiteCylinderGap L a M/2)/(finiteAlignment L M+cylinderRadius L M))
      atTop (nhds ((cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L))) ∧
    Tendsto (fun M => min 1 ((finiteCylinderGap L a M/2+cylinderRadius L M)/finiteAlignment L M))
      atTop (nhds ((cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L))) ∧
    Tendsto (fun M => min 1 ((finiteCylinderGap L a M/2+cylinderRadius L M)/finiteAlignment L M)-
      (finiteCylinderGap L a M/2)/(finiteAlignment L M+cylinderRadius L M)) atTop (nhds 0) := by
  have hLp : 0 < L := by omega
  have hN : Tendsto (fun M => finiteCylinderGap L a M/2) atTop
      (nhds ((cylinderMean L a+alignmentConstant L)/2)) := by
    simp only [finiteCylinderGap_eq]
    exact ((finiteCylinderMean_tendsto hLp a).add (finiteAlignment_tendsto hLp)).div_const 2
  have hx : ((cylinderMean L a+alignmentConstant L)/2)/alignmentConstant L ≤ 1 := by
    apply (div_le_one (alignmentConstant_pos hL)).mpr
    linarith [cylinderMean_upper hLp a]
  have h := ratio_enclosure_limits hN (finiteAlignment_tendsto hLp)
    (cylinderRadius_tendsto L) (cylinderRadius_tendsto L) (alignmentConstant_pos hL) hx
  have he : ((cylinderMean L a+alignmentConstant L)/2)/alignmentConstant L=
      (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L) := by ring
  simpa only [he] using h

theorem positionWeight_enclosure_limits {L : ℕ} (hL : 2 ≤ L) (k : ℕ) :
    Tendsto (fun M => positionNumerator L k/(finiteAlignment L M+cylinderRadius L M))
      atTop (nhds (positionWeight L k)) ∧
    Tendsto (fun M => min 1 (positionNumerator L k/finiteAlignment L M))
      atTop (nhds (positionWeight L k)) ∧
    Tendsto (fun M => min 1 (positionNumerator L k/finiteAlignment L M)-
      positionNumerator L k/(finiteAlignment L M+cylinderRadius L M)) atTop (nhds 0) := by
  have hLp : 0 < L := by omega
  have h := ratio_enclosure_limits (tendsto_const_nhds (x := positionNumerator L k))
    (finiteAlignment_tendsto hLp) (cylinderRadius_tendsto L) (tendsto_const_nhds (x := (0 : ℝ)))
    (alignmentConstant_pos hL) ((div_le_one (alignmentConstant_pos hL)).mpr
      (positionNumerator_le_alignment hLp k))
  simpa only [add_zero,← positionWeight_numerator hLp k] using h

theorem omittedPositionMass_upper_tendsto {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (fun M => min 1 (cylinderRadius L M/finiteAlignment L M)) atTop (nhds 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).min ((cylinderRadius_tendsto L).div
    (finiteAlignment_tendsto (by omega : 0 < L)) (alignmentConstant_pos hL).ne')
  simp only [zero_div,min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at h
  convert! h using 1

end NField.Alignment.CollisionPositionEnclosure
