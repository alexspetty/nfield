/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CanonicalCollisionSpectrum

/-! Exact witnesses establish the three printed first-three-hundred-prime systems. -/

namespace NField.Alignment.DisplayedPrimeSpectra

open scoped BigOperators
open EventualCollisionLabels CanonicalCollisionSpectrum TheStructureThatSurvives
open BlockSpectralMultiplicity CenteredCollisionSum

theorem prime_label_mem_first_of_lt {b ell p N : ℕ} (hp : p.Prime) (hpN : p < N) :
    directAllLagDeviation b ell p ∈ firstPrimeLabelSet b ell N := by
  apply Finset.mem_image.mpr
  refine ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr ((Nat.count_le _).trans_lt hpN), ?_⟩
  rw [Nat.nth_count hp]

theorem witness_image_subset_first {b ell N : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p < N) :
    P.image (directAllLagDeviation b ell) ⊆ firstPrimeLabelSet b ell N := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact prime_label_mem_first_of_lt (hP p hp).1 (hP p hp).2

set_option maxRecDepth 4000 in
/-- Title: `All base seven labels occur among the first three hundred primes`. -/
theorem base_seven_first_three_hundred_labels :
    firstPrimeLabelSet 7 1 300 = allPrimeLabelSet 7 1 := by
  let P : Finset ℕ := {43, 37, 31, 193, 19, 13, 5, 2, 3, 67, 61, 251}
  have hP : ∀ p ∈ P, p.Prime ∧ p < 300 := by decide +kernel
  have hlabels : P.image (directAllLagDeviation 7 1) = allPrimeLabelSet 7 1 := by decide +kernel
  apply Finset.Subset.antisymm (firstPrimeLabelSet_subset (by decide) (by decide) 300)
  rw [← hlabels]
  exact witness_image_subset_first P hP

set_option maxRecDepth 4000 in
/-- Title: `All base ten labels occur among the first three hundred primes`. -/
theorem base_ten_first_three_hundred_labels :
    firstPrimeLabelSet 10 1 300 = allPrimeLabelSet 10 1 := by
  let P : Finset ℕ := {191, 73, 41, 37, 23, 11, 2, 17, 3, 59, 127, 109}
  have hP : ∀ p ∈ P, p.Prime ∧ p < 300 := by decide +kernel
  have hlabels : P.image (directAllLagDeviation 10 1) = allPrimeLabelSet 10 1 := by decide +kernel
  apply Finset.Subset.antisymm (firstPrimeLabelSet_subset (by decide) (by decide) 300)
  rw [← hlabels]
  exact witness_image_subset_first P hP

set_option maxRecDepth 4000 in
/-- Title: `All base twelve labels occur among the first three hundred primes`. -/
theorem base_twelve_first_three_hundred_labels :
    firstPrimeLabelSet 12 1 300 = allPrimeLabelSet 12 1 := by
  let P : Finset ℕ := {277, 89, 61, 37, 79, 13, 2, 43, 31, 83, 199, 11}
  have hP : ∀ p ∈ P, p.Prime ∧ p < 300 := by decide +kernel
  have hlabels : P.image (directAllLagDeviation 12 1) = allPrimeLabelSet 12 1 := by decide +kernel
  apply Finset.Subset.antisymm (firstPrimeLabelSet_subset (by decide) (by decide) 300)
  rw [← hlabels]
  exact witness_image_subset_first P hP

/-- Title: `Each displayed prime system has twelve labels`. -/
theorem displayed_first_three_hundred_counts :
    (firstPrimeLabelSet 7 1 300).card = 12 ∧
    (firstPrimeLabelSet 10 1 300).card = 12 ∧
    (firstPrimeLabelSet 12 1 300).card = 12 := by
  rw [base_seven_first_three_hundred_labels, base_ten_first_three_hundred_labels,
    base_twelve_first_three_hundred_labels]
  decide +kernel

/-- Title: `Each displayed prime system has two hundred eighty eight bulk modes`.

All three printed particle Hamiltonians have exact bulk multiplicity two hundred eighty eight. -/
theorem displayed_bulk_multiplicities {τ : ℝ} (hτ : 0 < τ) :
    ((hamiltonian (firstPrimeAffinity 7 1 300 τ)).charpoly.roots).count 1 = 288 ∧
    ((hamiltonian (firstPrimeAffinity 10 1 300 τ)).charpoly.roots).count 1 = 288 ∧
    ((hamiltonian (firstPrimeAffinity 12 1 300 τ)).charpoly.roots).count 1 = 288 := by
  rw [first_prime_bulk_multiplicity 7 1 300 (by decide) hτ,
    first_prime_bulk_multiplicity 10 1 300 (by decide) hτ,
    first_prime_bulk_multiplicity 12 1 300 (by decide) hτ,
    displayed_first_three_hundred_counts.1, displayed_first_three_hundred_counts.2.1,
    displayed_first_three_hundred_counts.2.2]
  norm_num

end NField.Alignment.DisplayedPrimeSpectra
