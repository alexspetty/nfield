/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSuffixSecondMoments

/-!
# Integrability of the actual positive and inverse suffix energies

Uniform deterministic bounds on every prime factor give finite bounds
on each finite suffix product. These justify the ordinary real integrals
used in the exceptional-event Markov estimates.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSuffixIntegrability
open scoped BigOperators
open MeasureTheory SteinhausMoment HarperPrimeBlocks HarperPrimeBlockLaw
  HarperCriticalGoodEvent HarperEulerLogComparison HarperSuffixSecondMoments

theorem positive_factor_bound {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    ‖(1-primeTerm q t ω)⁻¹‖^2 ≤ 16 := by
  have hl := norm_sub_norm_le (1 : ℂ) (primeTerm q t ω)
  rw [norm_one] at hl
  have hb := primeTerm_norm_le hq t ω
  have hp : 0 < ‖1-primeTerm q t ω‖ := norm_pos_iff.mpr (localFactor_ne_zero hq t ω)
  have hi : ‖(1-primeTerm q t ω)⁻¹‖ ≤ 4 := by
    rw [norm_inv,← one_div ‖1-primeTerm q t ω‖,div_le_iff₀ hp]
    linarith
  nlinarith [norm_nonneg ((1-primeTerm q t ω)⁻¹)]

theorem inverse_factor_bound {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    ‖1-primeTerm q t ω‖^2 ≤ 4 := by
  have h := norm_sub_le (1 : ℂ) (primeTerm q t ω)
  rw [norm_one] at h
  have hb := primeTerm_norm_le hq t ω
  nlinarith [norm_nonneg (1-primeTerm q t ω)]

theorem suffix_positive_integrable (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) :
    Integrable (fun ω => ‖suffixProduct x M t j ω‖^2) phaseMeasure := by
  apply Integrable.of_bound ((suffixProduct_measurable x M t j).norm.pow_const 2).aestronglyMeasurable
    (∏ l ∈ Finset.Icc j M, ∏ _q ∈ primeBlock x l, (16 : ℝ))
  apply ae_of_all
  intro ω
  rw [Real.norm_of_nonneg (sq_nonneg _),suffixProduct,norm_prod,← Finset.prod_pow]
  apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
  intro l _
  rw [blockProduct,norm_prod,← Finset.prod_pow]
  exact Finset.prod_le_prod (fun _ _ => sq_nonneg _)
    (fun q hq => positive_factor_bound (primeBlock_mem.mp hq).1 _ ω)

theorem suffix_inverse_integrable (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) :
    Integrable (fun ω => ‖(suffixProduct x M t j ω)⁻¹‖^2) phaseMeasure := by
  apply Integrable.of_bound ((suffixProduct_measurable x M t j).inv.norm.pow_const 2).aestronglyMeasurable
    (∏ l ∈ Finset.Icc j M, ∏ _q ∈ primeBlock x l, (4 : ℝ))
  apply ae_of_all
  intro ω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change ‖(suffixProduct x M t j ω)⁻¹‖^2 ≤ _
  simp only [suffixProduct,blockProduct,Finset.prod_inv_distrib,inv_inv,norm_prod,← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro l _
    exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)
  · intro l _
    exact Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      (fun q hq => inverse_factor_bound (primeBlock_mem.mp hq).1 _ ω)

end NField.Alignment.HarperSuffixIntegrability
