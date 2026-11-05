/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerIncrement
import NField.Alignment.HarperFrequencyScales
import Mathlib.Data.Int.Interval

/-!
# The actual Euler-product grid error

The mean-square increment estimate is integrated over the full finite grid
with exact half-open cells. Its expectation is O(log(P)^(49/50)), uniformly
in the center, which implies the published exponent 99/100. Joint and
phase integrability, grid cardinality and fractional box bounds are proved.
At the rounded cutoff the grid scale is a genuine integer, and each sample
for the required central integer shifts is an actual conditioning frequency.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperEulerDiscretization
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSmoothCount
  HarperRandomEulerProduct HarperEulerIntegral HarperEulerSecondMoment HarperEulerIncrement
  HarperFrequencyScales HarperRoundedCutoff HarperConditioningDecay

def gridScale (P : ℝ) : ℝ := (Real.log P)^(101/100 : ℝ)
def gridCenters (D : ℝ) : Finset ℤ := Finset.Icc ⌈-(D/2)⌉ ⌊D/2⌋
def cellError (P u h : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ t in Set.Ioc (-h) h, incrementEnergy P u t ω
def gridError (P v : ℝ) (ω : PhaseSpace) : ℝ :=
  ∑ k ∈ gridCenters (gridScale P), cellError P (v+(k : ℝ)/gridScale P) (1/(2*gridScale P)) ω

theorem incrementEnergy_measurable (P u : ℝ) :
    Measurable (fun z : ℝ × PhaseSpace => incrementEnergy P u z.1 z.2) := by
  exact (((verticalProduct_measurable P (1/2)).comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)).sub
    ((eulerProduct_measurable P (linePoint (1/2) u)).comp measurable_snd)).norm.pow_const 2

theorem incrementEnergy_bound (P u t : ℝ) (ω : PhaseSpace) :
    incrementEnergy P u t ω ≤ (2*shiftedProduct P (1/2))^2 := by
  have h₁ := eulerProduct_norm_le P (s := linePoint (1/2) (u+t)) (by norm_num [linePoint_re]) ω
  have h₂ := eulerProduct_norm_le P (s := linePoint (1/2) u) (by norm_num [linePoint_re]) ω
  simp only [linePoint_re] at h₁ h₂
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by linarith)

theorem incrementEnergy_integrable (P u h : ℝ) :
    Integrable (fun z : ℝ × PhaseSpace => incrementEnergy P u z.1 z.2)
      ((volume.restrict (Set.Ioc (-h) h)).prod phaseMeasure) := by
  apply Integrable.of_bound (incrementEnergy_measurable P u).aestronglyMeasurable
    ((2*shiftedProduct P (1/2))^2)
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (show 0 ≤ incrementEnergy P u z.1 z.2 from sq_nonneg _)]
    exact incrementEnergy_bound P u z.1 z.2)

theorem incrementEnergy_integrable_line (P u h : ℝ) (ω : PhaseSpace) :
    Integrable (fun t => incrementEnergy P u t ω) (volume.restrict (Set.Ioc (-h) h)) := by
  apply Integrable.of_bound ((incrementEnergy_measurable P u).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    ((2*shiftedProduct P (1/2))^2)
  exact Filter.Eventually.of_forall (fun t => by
    change ‖incrementEnergy P u t ω‖ ≤ _
    rw [Real.norm_of_nonneg (show 0 ≤ incrementEnergy P u t ω from sq_nonneg _)]
    exact incrementEnergy_bound P u t ω)

theorem cellError_integrable (P u h : ℝ) : Integrable (cellError P u h) phaseMeasure :=
  (incrementEnergy_integrable P u h).integral_prod_right

theorem cellError_nonneg (P u h : ℝ) (ω : PhaseSpace) : 0 ≤ cellError P u h ω :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem cellError_expectation (P u h : ℝ) :
    (∫ ω, cellError P u h ω ∂phaseMeasure) =
      ∫ t in Set.Ioc (-h) h, ∫ ω, incrementEnergy P u t ω ∂phaseMeasure := by
  exact (integral_integral_swap (f := fun t ω => incrementEnergy P u t ω)
    (incrementEnergy_integrable P u h)).symm

theorem cellError_expectation_bound (P u : ℝ) {h B : ℝ} (hh : 0 ≤ h)
    (hb : ∀ t : ℝ, |t| ≤ h → (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) ≤ B) :
    (∫ ω, cellError P u h ω ∂phaseMeasure) ≤ 2*h*B := by
  rw [cellError_expectation]
  have hi := (incrementEnergy_integrable P u h).integral_prod_left
  calc
    _ ≤ ∫ _t in Set.Ioc (-h) h, B := by
      apply setIntegral_mono_on hi (integrable_const B) measurableSet_Ioc
      intro t ht
      exact hb t (abs_le.mpr ⟨ht.1.le,ht.2⟩)
    _ = _ := by
      rw [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le (by linarith)]
      simp only [smul_eq_mul]
      ring

theorem gridCenters_mem (D : ℝ) (k : ℤ) : k ∈ gridCenters D ↔ |(k : ℝ)| ≤ D/2 := by
  simp [gridCenters, Int.ceil_le, Int.le_floor, abs_le]

theorem gridCenters_card_bound {D : ℝ} (hD : 1 ≤ D) :
    ((gridCenters D).card : ℝ) ≤ 2*D := by
  have h0 : ⌈-(D/2)⌉ ≤ (0 : ℤ) := Int.ceil_le.mpr (by linarith)
  have h1 : (0 : ℤ) ≤ ⌊D/2⌋ := Int.le_floor.mpr (by linarith)
  rw [gridCenters, Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  push_cast
  have ha := Int.le_ceil (-(D/2))
  have hb := Int.floor_le (D/2)
  linarith

theorem gridError_integrable (P v : ℝ) : Integrable (gridError P v) phaseMeasure :=
  integrable_finsetSum _ (fun _k _ => cellError_integrable P _ _)

theorem gridError_nonneg (P v : ℝ) (ω : PhaseSpace) : 0 ≤ gridError P v ω :=
  Finset.sum_nonneg (fun _k _ => cellError_nonneg P _ _ ω)

theorem gridError_expectation_bound (P v : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hD : 1 ≤ gridScale P)
    (hb : ∀ u t : ℝ, |t| ≤ 1/(2*gridScale P) →
      (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) ≤ B) :
    (∫ ω, gridError P v ω ∂phaseMeasure) ≤ 2*B := by
  have hD0 : 0 < gridScale P := by linarith
  unfold gridError
  rw [integral_finsetSum _ (fun k _ => cellError_integrable P _ _)]
  calc
    _ ≤ ∑ _k ∈ gridCenters (gridScale P), 2*(1/(2*gridScale P))*B :=
      Finset.sum_le_sum (fun k _ => cellError_expectation_bound P _ (by positivity) (hb _))
    _ = ((gridCenters (gridScale P)).card : ℝ)/gridScale P*B := by simp; field_simp
    _ ≤ 2*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply (div_le_iff₀ hD0).mpr
      exact gridCenters_card_bound hD

theorem eventual_gridError_expectation_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ v : ℝ, (∫ ω, gridError P v ω ∂phaseMeasure) ≤ C*(Real.log P)^(49/50 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_small_increment_bound
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1] with P hbound hP
  intro v
  have hD : 1 ≤ gridScale P := Real.one_le_rpow hP (by norm_num)
  have h := gridError_expectation_bound P v
    (show 0 ≤ C*(Real.log P)^(49/50 : ℝ) by positivity) hD hbound
  convert h using 1
  ring

theorem gridScale_primeCutoff (x : ℝ) :
    gridScale (primeCutoff x) = ((cutoffRoot x)^101 : ℕ) := by
  rw [gridScale, log_primeCutoff, cutoffLog,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg _) 100]
  norm_num


theorem eventual_gridError_log99_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ v : ℝ, (∫ ω, gridError P v ω ∂phaseMeasure) ≤ C*(Real.log P)^(99/100 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_gridError_expectation_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1] with P hbound hP
  intro v
  exact (hbound v).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (49/50 : ℝ) ≤ 99/100)) hC.le)

theorem actual_grid_center_is_conditioning_frequency {x : ℝ} (hx : 0 < cutoffRoot x)
    (v k : ℤ) (hv : |(v : ℝ)| ≤ (cutoffRoot x : ℝ))
    (hk : k ∈ gridCenters (gridScale (primeCutoff x))) :
    ∃ i : Fin (factorCount x), HarperConditioningFrequencies.frequency x i =
      (v : ℝ)+(k : ℝ)/gridScale (primeCutoff x) := by
  let d : ℕ := (cutoffRoot x)^101
  let j : ℤ := v*(d : ℤ)+k
  have hr : (1 : ℝ) ≤ cutoffRoot x := by exact_mod_cast hx
  have hd : (0 : ℝ) < d := by exact_mod_cast (pow_pos hx 101)
  have hg : gridScale (primeCutoff x) = (d : ℝ) := gridScale_primeCutoff x
  have hk' : |(k : ℝ)| ≤ (d : ℝ)/2 := by simpa only [gridCenters_mem, hg] using hk
  have hjR : |(j : ℝ)| ≤ (frequencyRadius x : ℝ) := by
    calc
      _ = |(v : ℝ)*(d : ℝ)+(k : ℝ)| := by simp only [j, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      _ ≤ |(v : ℝ)| *(d : ℝ)+|(k : ℝ)| := by
        simpa only [abs_mul, abs_of_pos hd] using abs_add_le ((v : ℝ)*(d : ℝ)) (k : ℝ)
      _ ≤ (cutoffRoot x : ℝ)*(d : ℝ)+(d : ℝ)/2 :=
        add_le_add (mul_le_mul_of_nonneg_right hv hd.le) hk'
      _ ≤ 2*(cutoffRoot x : ℝ)*(d : ℝ) := by nlinarith
      _ = _ := by simp only [frequencyRadius, d, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; ring
  have hj : -(frequencyRadius x : ℤ) ≤ j ∧ j ≤ (frequencyRadius x : ℤ) := by
    have h := abs_le.mp hjR
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  obtain ⟨i,hi⟩ := HarperConditioningFrequencies.frequencyIndex_covers x j hj.1 hj.2
  refine ⟨i,?_⟩
  have hden : (cutoffLog x)^(101/100 : ℝ) = (d : ℝ) := by
    simpa only [gridScale, log_primeCutoff] using hg
  rw [HarperConditioningFrequencies.frequency, hi, hden, hg]
  simp only [j, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp

theorem eventual_gridError_conditioning_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (p : ℕ), 0 < cutoffLog ((p : ℝ)-1) →
    ∀ (c1 c2 : HarperActualConditioning.Coefficients p) (v : ℝ),
      HarperSmoothingConditioning.boxConditioning p c1 c2 (gridError P v) ≤
        C*(Real.log P)^(147/200 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_gridError_expectation_bound
  refine ⟨C^(3/4 : ℝ), Real.rpow_pos_of_pos hC _, ?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 0] with P hbound hP
  intro p hell c1 c2 v
  calc
    _ ≤ (∫ ω, gridError P v ω ∂phaseMeasure)^(3/4 : ℝ) :=
      HarperFrequencyIntervals.boxConditioning_le_expectation hell c1 c2
        (gridError_integrable P v) (gridError_nonneg P v)
    _ ≤ (C*(Real.log P)^(49/50 : ℝ))^(3/4 : ℝ) := Real.rpow_le_rpow
      (integral_nonneg (gridError_nonneg P v)) (hbound v) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hP _), ← Real.rpow_mul hP]
      norm_num

end NField.Alignment.HarperEulerDiscretization
