/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianBarrier

/-!
# Gaussian interval mass under independent random shifts

The density bound is uniform in interval location. The exact finite
endpoint law therefore controls an endpoint plus any independent
measurable shift, without a distributional assumption on that shift.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianIntervalMass
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperGaussianEndpoint HarperGaussianEndpointLaw

theorem gaussian_interval_mass {v : NNReal} (hv : 0 < v) (b : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    (gaussianReal 0 v).real (Icc b (b+c)) ≤ c/Real.sqrt v := by
  rw [gaussian_mass_density 0 hv]
  calc
    _ ≤ ∫ _ in Icc b (b+c), (1/Real.sqrt (v : ℝ)) := by
      apply integral_mono (integrable_gaussianPDFReal 0 v).integrableOn
        (integrableOn_const (μ := volume) (s := Icc b (b+c))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact gaussian_density_le_inv_sqrt hv
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : b ≤ b+c)]
      simp [div_eq_mul_inv]

theorem gaussian_sum_interval_law {n : ℕ} (v : Fin n → NNReal) (a b : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real {z | a ≤ (∑ i, z i) ∧ (∑ i, z i) ≤ b} =
      (gaussianReal 0 (∑ i, v i)).real (Icc a b) := by
  have hm : Measurable (fun z : Fin n → ℝ => ∑ i, z i) := by fun_prop
  simp only [measureReal_def]
  rw [← gaussian_sum_law v,Measure.map_apply hm measurableSet_Icc]
  rfl

theorem gaussian_sum_interval_mass {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i) (b : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      {z | b ≤ (∑ i, z i) ∧ (∑ i, z i) ≤ b+c} ≤ 2*c/Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : (n : ℝ)/4 ≤ (∑ i, v i : NNReal) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hv i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      NNReal.coe_sum,div_eq_mul_inv,one_mul] using h
  have hV0 : (0 : ℝ) < (∑ i, v i : NNReal) := by linarith
  have hs : Real.sqrt (n : ℝ)/2 ≤ Real.sqrt (∑ i, v i : NNReal) := by
    nlinarith [Real.sq_sqrt hn0.le,Real.sq_sqrt (show (0 : ℝ) ≤ (∑ i, v i : NNReal) by positivity),
      Real.sqrt_nonneg (n : ℝ),Real.sqrt_nonneg ((∑ i, v i : NNReal) : ℝ)]
  rw [gaussian_sum_interval_law]
  apply (gaussian_interval_mass (show 0 < (∑ i, v i : NNReal) from hV0) b hc).trans
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hV0) (Real.sqrt_pos.mpr hn0)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hs hc]

theorem gaussian_sum_random_shift_interval {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (g : β → ℝ) (hg : Measurable g)
    {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ((Measure.pi (fun i => gaussianReal 0 (v i))).prod ν).real
      {p | b ≤ (∑ i, p.1 i)+g p.2 ∧ (∑ i, p.1 i)+g p.2 ≤ b+c} ≤
        2*c/Real.sqrt (n : ℝ) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  let A : Set ((Fin n → ℝ) × β) :=
    {p | b ≤ (∑ i, p.1 i)+g p.2 ∧ (∑ i, p.1 i)+g p.2 ≤ b+c}
  have hm : Measurable (fun p : (Fin n → ℝ) × β => (∑ i, p.1 i)+g p.2) := by fun_prop
  have hA : MeasurableSet A := (measurableSet_le measurable_const hm).inter
    (measurableSet_le hm measurable_const)
  have hf : Integrable (A.indicator (1 : ((Fin n → ℝ) × β) → ℝ)) (μ.prod ν) :=
    (integrable_const 1).indicator hA
  have hinner (z : β) : (∫ y, A.indicator 1 (y,z) ∂μ) ≤ 2*c/Real.sqrt (n : ℝ) := by
    let B : Set (Fin n → ℝ) := {y | b-g z ≤ (∑ i, y i) ∧ (∑ i, y i) ≤ (b-g z)+c}
    have he (y : Fin n → ℝ) : (y,z) ∈ A ↔ y ∈ B := by
      change (b ≤ (∑ i, y i)+g z ∧ (∑ i, y i)+g z ≤ b+c) ↔
        (b-g z ≤ (∑ i, y i) ∧ (∑ i, y i) ≤ (b-g z)+c)
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    have hfun : (fun y => A.indicator (1 : ((Fin n → ℝ) × β) → ℝ) (y,z)) = B.indicator 1 := by
      funext y
      by_cases hy : y ∈ B <;> simp [Set.indicator,he,hy]
    have hB : MeasurableSet B := by
      have hsum : Measurable (fun y : Fin n → ℝ => ∑ i, y i) := by fun_prop
      exact (measurableSet_le measurable_const hsum).inter (measurableSet_le hsum measurable_const)
    rw [hfun,integral_indicator_one hB]
    exact gaussian_sum_interval_mass hn v hv (b-g z) hc
  change (μ.prod ν).real A ≤ _
  rw [← integral_indicator_one hA,integral_prod_symm _ hf]
  calc
    _ ≤ ∫ _ : β, 2*c/Real.sqrt (n : ℝ) ∂ν :=
      integral_mono hf.integral_prod_right (integrable_const _) hinner
    _ = _ := by simp

end NField.Alignment.HarperGaussianIntervalMass
