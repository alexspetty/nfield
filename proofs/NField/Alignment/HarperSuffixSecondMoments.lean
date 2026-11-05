/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperUnweightedCoordinateProducts

/-!
# Actual suffix Euler-product second moments

The recursive frequencies remain in the literal suffix products. Their
deterministic values disappear only after each independent prime factor
is integrated. Both the product and its inverse have a squared-norm
moment bounded by the full prime-product normalizer at the first block.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSuffixSecondMoments
open scoped BigOperators
open MeasureTheory SteinhausMoment HarperPrimeBlocks HarperPrimeBlockLaw
  HarperCriticalGoodEvent HarperFrequencyMesh HarperEulerIntegral HarperEulerLogComparison
  HarperTiltedFactors HarperTiltedNormalizer HarperUnweightedFactors
  HarperUnweightedCoordinateProducts HarperSmoothCount CollisionMertensInput

theorem suffixProduct_measurable (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) :
    Measurable (suffixProduct x M t j) :=
  Finset.measurable_prod _ (fun l _ => blockProduct_measurable x l _)

theorem suffix_energy_eq_nested (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) :
    ‖suffixProduct x M t j ω‖^2 =
      ∏ l ∈ Finset.Icc j M, ∏ q ∈ primeBlock x l,
        localEnergy q (linePoint (1/2) (approximation x t l)) (ω q) := by
  rw [suffixProduct,norm_prod,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  rw [blockProduct,norm_prod,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q hq
  simp only [localEnergy,primeTerm,steinhaus_prime (primeBlock_mem.mp hq).1,phase]

theorem suffix_inverse_energy_eq_nested (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) :
    ‖(suffixProduct x M t j ω)⁻¹‖^2 =
      ∏ l ∈ Finset.Icc j M, ∏ q ∈ primeBlock x l,
        inverseEnergy q (approximation x t l) (ω q) := by
  simp only [suffixProduct,blockProduct,Finset.prod_inv_distrib,inv_inv,norm_prod,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro q hq
  simp only [inverseEnergy,primeTerm,steinhaus_prime (primeBlock_mem.mp hq).1,phase]

theorem suffix_positive_moment {x : ℝ} (hx : 1 ≤ x) (M : ℕ) (t : ℝ) (j : ℕ) :
    (∫ ω, ‖suffixProduct x M t j ω‖^2 ∂phaseMeasure) =
      ∏ l ∈ Finset.Icc j M, ∏ q ∈ primeBlock x l, (1-(q : ℝ)⁻¹)⁻¹ := by
  simp_rw [suffix_energy_eq_nested]
  rw [integral_nested_coordinates _ _
    (fun _ _ _ _ hne => primeBlock_pairwise_disjoint hx hne)
    (fun l q => localEnergy q (linePoint (1/2) (approximation x t l)))
    (fun _ q => localEnergy_measurable q _)]
  apply Finset.prod_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro q hq
  change localMass q (linePoint (1/2) (approximation x t l)) = _
  rw [localMass_eq (primeBlock_mem.mp hq).1 (by norm_num [linePoint])]
  norm_num [linePoint,Real.rpow_neg_one]

theorem suffix_inverse_moment {x : ℝ} (hx : 1 ≤ x) (M : ℕ) (t : ℝ) (j : ℕ) :
    (∫ ω, ‖(suffixProduct x M t j ω)⁻¹‖^2 ∂phaseMeasure) =
      ∏ l ∈ Finset.Icc j M, ∏ q ∈ primeBlock x l, (1+(q : ℝ)⁻¹) := by
  simp_rw [suffix_inverse_energy_eq_nested]
  rw [integral_nested_coordinates _ _
    (fun _ _ _ _ hne => primeBlock_pairwise_disjoint hx hne)
    (fun l q => inverseEnergy q (approximation x t l)) (fun _ q => inverseEnergy_measurable q _)]
  apply Finset.prod_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro q hq
  exact inverseEnergy_integral (primeBlock_mem.mp hq).1 _

theorem suffix_prime_normalizer_le {x : ℝ} (hx : 1 ≤ x) (M j : ℕ) :
    (∏ l ∈ Finset.Icc j M, ∏ q ∈ primeBlock x l, (1-(q : ℝ)⁻¹)⁻¹) ≤
      inversePrimeProduct (blockUpper x j) := by
  classical
  rw [← Finset.prod_biUnion (fun _ _ _ _ hne => primeBlock_pairwise_disjoint hx hne)]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro q hq
    obtain ⟨l,hl,hql⟩ := Finset.mem_biUnion.mp hq
    exact primesUpTo_mem.mpr ⟨(primeBlock_mem.mp hql).1,
      (primeBlock_mem.mp hql).2.2.trans (blockUpper_antitone hx (Finset.mem_Icc.mp hl).1)⟩
  · intro q hq
    obtain ⟨l,_,hql⟩ := Finset.mem_biUnion.mp hq
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (prime_positive_mass_ge_one (primeBlock_mem.mp hql).1)
  · intro q hq _
    exact prime_positive_mass_ge_one (primesUpTo_mem.mp hq).1

theorem suffix_positive_moment_le {x : ℝ} (hx : 1 ≤ x) (M : ℕ) (t : ℝ) (j : ℕ) :
    (∫ ω, ‖suffixProduct x M t j ω‖^2 ∂phaseMeasure) ≤
      inversePrimeProduct (blockUpper x j) := by
  rw [suffix_positive_moment hx]
  exact suffix_prime_normalizer_le hx M j

theorem suffix_inverse_moment_le {x : ℝ} (hx : 1 ≤ x) (M : ℕ) (t : ℝ) (j : ℕ) :
    (∫ ω, ‖(suffixProduct x M t j ω)⁻¹‖^2 ∂phaseMeasure) ≤
      inversePrimeProduct (blockUpper x j) := by
  rw [suffix_inverse_moment hx]
  apply le_trans _ (suffix_prime_normalizer_le hx M j)
  apply Finset.prod_le_prod
  · intro l _
    exact Finset.prod_nonneg (fun q _ => by positivity)
  · intro l _
    exact Finset.prod_le_prod (fun q _ => by positivity)
      (fun q hq => prime_inverse_mass_bound (primeBlock_mem.mp hq).1)

end NField.Alignment.HarperSuffixSecondMoments
