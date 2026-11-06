/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryDiagonalDefinitions
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Bounded periodic primitives with the manuscript's raw sawtooth convention -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryBernoulliPrimitive
open MeasureTheory Filter Set StationaryDiagonalDefinitions

def firstPrimitive (x : ℝ) : ℝ :=
  (Int.fract x ^ 2 - Int.fract x + 1 / 6) / 2
def secondPrimitive (x : ℝ) : ℝ :=
  (Int.fract x ^ 3 - 3 / 2 * Int.fract x ^ 2 + 1 / 2 * Int.fract x) / 6

theorem psi_abs_bound (x : ℝ) : |psi x| ≤ 1 / 2 := by
  unfold psi
  exact abs_le.mpr ⟨by linarith [Int.fract_nonneg x], by linarith [Int.fract_lt_one x]⟩

theorem psi_measurable : Measurable psi := measurable_fract.sub measurable_const

theorem psi_interval_integrable (a b : ℝ) : IntervalIntegrable psi volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume a b).mono_fun'
  · exact psi_measurable.aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using psi_abs_bound x)

theorem firstPrimitive_continuous : Continuous firstPrimitive := by
  have hp : ContinuousOn (fun u : ℝ => (u ^ 2 - u + 1 / 6) / 2) (Icc 0 1) := by fun_prop
  exact hp.comp_fract'' (by norm_num)

theorem secondPrimitive_continuous : Continuous secondPrimitive := by
  have hp : ContinuousOn (fun u : ℝ => (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) / 6) (Icc 0 1) := by fun_prop
  exact hp.comp_fract'' (by norm_num)

/-- Title: `The quadratic Bernoulli primitive is uniformly bounded`. -/
theorem firstPrimitive_abs_bound (x : ℝ) : |firstPrimitive x| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  have hprod := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hsq := sq_nonneg (Int.fract x - 1 / 2)
  unfold firstPrimitive
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem secondPrimitive_abs_bound (x : ℝ) : |secondPrimitive x| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  have h2 : Int.fract x ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h3 : Int.fract x ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have h20 := sq_nonneg (Int.fract x)
  have h30 : 0 ≤ Int.fract x ^ 3 := by positivity
  unfold secondPrimitive
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem fract_right_eventually_affine (x : ℝ) :
    Int.fract =ᶠ[nhdsWithin x (Ioi x)] (fun y : ℝ => y - (⌊x⌋ : ℤ)) := by
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (Int.lt_floor_add_one x)), self_mem_nhdsWithin] with y hy hx
  have hf : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨(Int.floor_le x).trans hx.le, hy⟩
  simp only [Int.fract, hf]

/-- Title: `The Bernoulli primitive has the raw sawtooth as its right derivative at every point`. -/
theorem firstPrimitive_right_derivative (x : ℝ) :
    HasDerivWithinAt firstPrimitive (psi x) (Ioi x) x := by
  let z : ℝ := (⌊x⌋ : ℤ)
  have hd := (((((hasDerivAt_id x).sub_const z).pow 2).sub
    ((hasDerivAt_id x).sub_const z)).add_const (1 / 6)).div_const 2
  have he : firstPrimitive =ᶠ[nhdsWithin x (Ioi x)]
      (fun y : ℝ => ((y - z) ^ 2 - (y - z) + 1 / 6) / 2) := by
    filter_upwards [fract_right_eventually_affine x] with y hy
    simp only [firstPrimitive, hy, z]
  have hx : firstPrimitive x = ((x - z) ^ 2 - (x - z) + 1 / 6) / 2 := rfl
  have hh := hd.hasDerivWithinAt.congr_of_eventuallyEq he hx
  convert! hh using 1
  simp only [psi, Int.fract, z, id_eq]
  ring

theorem secondPrimitive_right_derivative (x : ℝ) :
    HasDerivWithinAt secondPrimitive (firstPrimitive x) (Ioi x) x := by
  let z : ℝ := (⌊x⌋ : ℤ)
  have h := (hasDerivAt_id x).sub_const z
  have hd := (((h.pow 3).sub ((h.pow 2).const_mul (3 / 2))).add (h.const_mul (1 / 2))).div_const 6
  have he : secondPrimitive =ᶠ[nhdsWithin x (Ioi x)]
      (fun y : ℝ => ((y - z) ^ 3 - 3 / 2 * (y - z) ^ 2 + 1 / 2 * (y - z)) / 6) := by
    filter_upwards [fract_right_eventually_affine x] with y hy
    simp only [secondPrimitive, hy, z]
  have hx : secondPrimitive x = ((x - z) ^ 3 - 3 / 2 * (x - z) ^ 2 + 1 / 2 * (x - z)) / 6 := rfl
  have hh := hd.hasDerivWithinAt.congr_of_eventuallyEq he hx
  convert! hh using 1
  simp only [firstPrimitive, Int.fract, z, id_eq]
  ring

theorem integral_psi (a b : ℝ) :
    (∫ u in a..b, psi u) = firstPrimitive b - firstPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right firstPrimitive_continuous.continuousOn
    (fun x _ => firstPrimitive_right_derivative x) (psi_interval_integrable a b)

theorem integral_firstPrimitive (a b : ℝ) :
    (∫ u in a..b, firstPrimitive u) = secondPrimitive b - secondPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right secondPrimitive_continuous.continuousOn
    (fun x _ => secondPrimitive_right_derivative x) (firstPrimitive_continuous.intervalIntegrable a b)

theorem firstPrimitive_integer (n : ℤ) : firstPrimitive n = 1 / 12 := by norm_num [firstPrimitive]
theorem secondPrimitive_integer (n : ℤ) : secondPrimitive n = 0 := by norm_num [secondPrimitive]

end NField.Alignment.StationaryBernoulliPrimitive
