/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DisplayedPrimeSpectra
import NField.Alignment.ExponentialKernelSourceIdentities

/-! Ordered eigenvalues, the literal diagonal normalization, and actual nontrivial mode counts. -/

namespace NField.Alignment.CollisionSpectrumSourceDetails

open scoped BigOperators Classical
open Filter Matrix ExponentialSpectralQuotient ConcreteCollisionBlocks
  ConcreteCollisionSpectrum CanonicalCollisionSpectrum EventualCollisionLabels BlockSpectralMultiplicity

/-- Title: `The diagonal scale is the square root of population over degree`. -/
theorem scale_sqrt_ratio {ι : Type*} [Fintype ι] (x pop : ι → ℝ) (τ : ℝ)
    (hp : ∀ i, 0 < pop i) (i : ι) :
    scale x pop τ i = Real.sqrt (pop i / degree x pop τ i) := by
  exact (Real.sqrt_div (hp i).le _).symm

/-- Title: `The particle affinity has the printed degree normalization`. -/
theorem particle_diagonal_normalization {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (label : ι → κ) (x : κ → ℝ) (τ : ℝ) :
    particleNormalized label x τ =
      diagonal (fun i => (Real.sqrt (particleDegree label x τ i))⁻¹) *
        ExponentialDistanceKernel.kernel (x ∘ label) τ *
          diagonal (fun i => (Real.sqrt (particleDegree label x τ i))⁻¹) := by
  ext i j
  have hd : 0 ≤ particleDegree label x τ i :=
    Finset.sum_nonneg (fun j hj => (ExponentialDistanceKernel.kernel_pos _ _ _ _).le)
  simp only [particleNormalized, Matrix.mul_diagonal, Matrix.diagonal_mul, Real.sqrt_mul hd]
  ring

/-- Title: `The ordered quotient eigenvalues decrease strictly from one`. -/
theorem quotient_ordered_spectrum {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    let hQ := (quotient_posDef x pop hx hp hτ).isHermitian
    StrictAnti hQ.eigenvalues₀ ∧ hQ.eigenvalues₀ 0 = 1 ∧ ∀ i, 0 < hQ.eigenvalues₀ i := by
  dsimp only
  let hQ := (quotient_posDef x pop hx hp hτ).isHermitian
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))
  have he (i : Fin (Fintype.card (Fin (n + 1)))) : hQ.eigenvalues (e i) = hQ.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hinj : Function.Injective hQ.eigenvalues₀ := by
    intro i j hij
    apply e.injective
    apply quotient_eigenvalues_injective x pop hx hp hτ
    rwa [he, he]
  have hanti := hQ.eigenvalues₀_antitone.strictAnti_of_injective hinj
  refine ⟨hanti, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := quotient_exists_eigenvalue_one x pop hx hp hτ
    have heq : hQ.eigenvalues₀ (e.symm i) = 1 := by
      rw [← he, e.apply_symm_apply]
      exact hi
    have hlo : 1 ≤ hQ.eigenvalues₀ 0 := by
      rw [← heq]
      exact hQ.eigenvalues₀_antitone (Fin.zero_le _)
    have hhi : hQ.eigenvalues₀ 0 ≤ 1 := by
      rw [← he]
      exact (quotient_eigenvalues_bounds x pop hx hp hτ _).2
    exact le_antisymm hhi hlo
  · intro i
    rw [← he]
    exact (quotient_eigenvalues_bounds x pop hx hp hτ _).1

noncomputable def nontrivialModeCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℕ := (hamiltonian A).charpoly.roots.countP (fun μ => μ ≠ 1)

/-- Title: `The number of nontrivial modes equals the actual label count`. -/
theorem integer_nontrivial_mode_count {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : ι → ℤ) {τ : ℝ} (hτ : 0 < τ) :
    nontrivialModeCount (integerAffinity s τ) = (Finset.univ.image s).card := by
  have hH := hamiltonian_isHermitian (particleNormalized_isHermitian id (fun i => (s i : ℝ)) τ)
  change (hamiltonian (integerAffinity s τ)).IsHermitian at hH
  have hc : (hamiltonian (integerAffinity s τ)).charpoly.roots.card = Fintype.card ι := by
    rw [hH.roots_charpoly_eq_eigenvalues]
    simp
  have hsplit := Multiset.card_eq_countP_add_countP (fun μ : ℝ => 1 = μ)
    (hamiltonian (integerAffinity s τ)).charpoly.roots
  have hcount := integer_bulk_multiplicity s hτ
  change (hamiltonian (integerAffinity s τ)).charpoly.roots.countP (fun μ => 1 = μ) =
    Fintype.card ι - (Finset.univ.image s).card at hcount
  have hle : (Finset.univ.image s).card ≤ Fintype.card ι :=
    (Finset.card_image_le).trans (by simp)
  change (hamiltonian (integerAffinity s τ)).charpoly.roots.countP (fun μ => μ ≠ 1) = _
  simp only [hc, ne_comm] at hsplit
  omega

theorem first_prime_nontrivial_mode_count (b ell N : ℕ) (hN : 0 < N) {τ : ℝ} (hτ : 0 < τ) :
    nontrivialModeCount (firstPrimeAffinity b ell N τ) = (firstPrimeLabelSet b ell N).card := by
  letI : NeZero N := ⟨ne_of_gt hN⟩
  have h := integer_nontrivial_mode_count
    (fun i : Fin N => CenteredCollisionSum.directAllLagDeviation b ell (Nat.nth Nat.Prime i.val)) hτ
  simpa only [firstPrimeAffinity, fin_prime_labels_eq] using h

/-- Title: `The finite table bounds every first prime spectrum`. -/
theorem first_prime_nontrivial_mode_bound {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (N : ℕ) (hN : 0 < N) {τ : ℝ} (hτ : 0 < τ) :
    nontrivialModeCount (firstPrimeAffinity b ell N τ) ≤ (allPrimeLabelSet b ell).card := by
  rw [first_prime_nontrivial_mode_count b ell N hN hτ]
  exact firstPrimeLabelSet_card_le hb hell N

/-- Title: `The actual proportion of nontrivial prime modes tends to zero`. -/
theorem actual_nontrivial_proportion_tendsto_zero {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell)
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun N : ℕ => (nontrivialModeCount (firstPrimeAffinity b ell N τ) : ℝ) / N)
      atTop (nhds 0) := by
  apply Filter.Tendsto.congr' _ (nontrivial_mode_proportion_tendsto_zero hb hell)
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [first_prime_nontrivial_mode_count b ell N hN hτ]

end NField.Alignment.CollisionSpectrumSourceDetails
