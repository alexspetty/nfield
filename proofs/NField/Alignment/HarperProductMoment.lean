/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEvenMomentBound
import Mathlib.Analysis.MeanInequalities

/-!
# Products controlled by a common higher moment

The equal-exponent arithmetic-geometric mean inequality bounds a product
of j nonnegative factors by the average of their jth powers. After multiplying
by the nonnegative short-sum weight and integrating, a common bound on the
jth moments bounds the product with no extra factor depending on j. This is
the equal-bound case of the Holder step needed for Taylor remainder products.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperProductMoment

open scoped BigOperators
open MeasureTheory SpectralRepulsion

theorem prod_le_power_average {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (u : ι → ℝ) (hu : ∀ i ∈ t, 0 ≤ u i) :
    (∏ i ∈ t, u i) ≤ (∑ i ∈ t, u i ^ t.card) / (t.card : ℝ) := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hw : (∑ _i ∈ t, (1 : ℝ) / t.card) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h := Real.geom_mean_le_arith_mean_weighted t (fun _ => (1 : ℝ) / t.card)
    (fun i => u i ^ t.card) (fun _ _ => by positivity) hw
    (fun i hi => pow_nonneg (hu i hi) _)
  have he (i : ι) (hi : i ∈ t) : (u i ^ t.card : ℝ) ^ ((1 : ℝ) / t.card) = u i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hu i hi)]
    have hh : (t.card : ℝ) * ((1 : ℝ) / t.card) = 1 := by field_simp
    rw [hh, Real.rpow_one]
  calc
    _ = ∏ i ∈ t, (u i ^ t.card : ℝ) ^ ((1 : ℝ) / t.card) :=
      Finset.prod_congr rfl (fun i hi => (he i hi).symm)
    _ ≤ _ := h
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem weighted_prod_le_power_average {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (u : ι → ℝ) (hu : ∀ i ∈ t, 0 ≤ u i) {W : ℝ} (hW : 0 ≤ W) :
    W * (∏ i ∈ t, u i) ≤ (∑ i ∈ t, W * u i ^ t.card) / (t.card : ℝ) := by
  calc
    _ ≤ W * ((∑ i ∈ t, u i ^ t.card) / (t.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (prod_le_power_average t ht u hu) hW
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem weighted_product_integrable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t : Finset ι) (ht : t.Nonempty) (W : Ω → ℝ) (u : ι → Ω → ℝ)
    (hW : ∀ ω, 0 ≤ W ω) (hu : ∀ i ∈ t, ∀ ω, 0 ≤ u i ω)
    (hWm : Measurable W) (hum : ∀ i ∈ t, Measurable (u i))
    (hI : ∀ i ∈ t, Integrable (fun ω => W ω * u i ω ^ t.card) μ) :
    Integrable (fun ω => W ω * ∏ i ∈ t, u i ω) μ := by
  apply ((integrable_finsetSum t hI).div_const (t.card : ℝ)).mono'
    (hWm.mul (Finset.measurable_prod t hum)).aestronglyMeasurable
  filter_upwards with ω
  change ‖W ω * ∏ i ∈ t, u i ω‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW ω)
    (Finset.prod_nonneg (fun i hi => hu i hi ω)))]
  exact weighted_prod_le_power_average t ht (fun i => u i ω) (fun i hi => hu i hi ω) (hW ω)

theorem integral_weighted_product_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t : Finset ι) (ht : t.Nonempty) (W : Ω → ℝ) (u : ι → Ω → ℝ)
    (hW : ∀ ω, 0 ≤ W ω) (hu : ∀ i ∈ t, ∀ ω, 0 ≤ u i ω)
    (hWm : Measurable W) (hum : ∀ i ∈ t, Measurable (u i))
    (hI : ∀ i ∈ t, Integrable (fun ω => W ω * u i ω ^ t.card) μ) :
    (∫ ω, W ω * ∏ i ∈ t, u i ω ∂μ) ≤
      (∑ i ∈ t, ∫ ω, W ω * u i ω ^ t.card ∂μ) / (t.card : ℝ) := by
  calc
    _ ≤ ∫ ω, (∑ i ∈ t, W ω * u i ω ^ t.card) / (t.card : ℝ) ∂μ :=
      integral_mono (weighted_product_integrable t ht W u hW hu hWm hum hI)
        ((integrable_finsetSum t hI).div_const _) (fun ω =>
          weighted_prod_le_power_average t ht (fun i => u i ω) (fun i hi => hu i hi ω) (hW ω))
    _ = _ := by rw [integral_div, integral_finsetSum t hI]

theorem integral_weighted_product_le_common {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t : Finset ι) (ht : t.Nonempty) (W : Ω → ℝ) (u : ι → Ω → ℝ)
    (hW : ∀ ω, 0 ≤ W ω) (hu : ∀ i ∈ t, ∀ ω, 0 ≤ u i ω)
    (hWm : Measurable W) (hum : ∀ i ∈ t, Measurable (u i))
    (hI : ∀ i ∈ t, Integrable (fun ω => W ω * u i ω ^ t.card) μ)
    {C : ℝ} (hC : ∀ i ∈ t, (∫ ω, W ω * u i ω ^ t.card ∂μ) ≤ C) :
    (∫ ω, W ω * ∏ i ∈ t, u i ω ∂μ) ≤ C := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  calc
    _ ≤ _ := integral_weighted_product_le t ht W u hW hu hWm hum hI
    _ ≤ (∑ _i ∈ t, C) / (t.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hC) hc.le
    _ = C := by simp [Finset.sum_const, nsmul_eq_mul, hc.ne']

theorem average_weighted_product_le {Ω ι : Type*} [Fintype Ω]
    (t : Finset ι) (ht : t.Nonempty) (W : Ω → ℝ) (u : ι → Ω → ℝ)
    (hW : ∀ ω, 0 ≤ W ω) (hu : ∀ i ∈ t, ∀ ω, 0 ≤ u i ω) :
    uniformAverage (fun ω => W ω * ∏ i ∈ t, u i ω) ≤
      (∑ i ∈ t, uniformAverage (fun ω => W ω * u i ω ^ t.card)) / (t.card : ℝ) := by
  unfold uniformAverage
  calc
    _ ≤ (Fintype.card Ω : ℝ)⁻¹ *
        (∑ ω, (∑ i ∈ t, W ω * u i ω ^ t.card) / (t.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ =>
        weighted_prod_le_power_average t ht (fun i => u i ω) (fun i hi => hu i hi ω) (hW ω)))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.sum_div, Finset.sum_comm, ← Finset.mul_sum]; ring

theorem average_weighted_product_le_common {Ω ι : Type*} [Fintype Ω]
    (t : Finset ι) (ht : t.Nonempty) (W : Ω → ℝ) (u : ι → Ω → ℝ)
    (hW : ∀ ω, 0 ≤ W ω) (hu : ∀ i ∈ t, ∀ ω, 0 ≤ u i ω)
    {C : ℝ} (hC : ∀ i ∈ t, uniformAverage (fun ω => W ω * u i ω ^ t.card) ≤ C) :
    uniformAverage (fun ω => W ω * ∏ i ∈ t, u i ω) ≤ C := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  calc
    _ ≤ _ := average_weighted_product_le t ht W u hW hu
    _ ≤ (∑ _i ∈ t, C) / (t.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hC) hc.le
    _ = C := by simp [Finset.sum_const, nsmul_eq_mul, hc.ne']

end NField.Alignment.HarperProductMoment
