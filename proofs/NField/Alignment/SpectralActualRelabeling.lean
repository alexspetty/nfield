/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralCharacterDistributions

/-! # Relabeling the actual conjugate-pair masses -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SpectralActualRelabeling
open scoped BigOperators
open SpectralRepulsion SpectralCharacterPairs SpectralCharacterDistributions

theorem pair_nonempty {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) : Nonempty (Pairs b) := by
  have hb1 : 0 < b - 1 := by have := hb.one_lt; omega
  have hc : 0 < (Fintype.card (Pairs b) : ℝ) := by
    rw [pair_population hb hbodd]
    positivity
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hc)

def statistic (b : ℕ) [NeZero b] [NeZero (b ^ 2)] (X : ℝ) (π : Equiv.Perm (Pairs b)) : ℝ :=
  relabelingStatistic (collisionPairMass b) (primePairMass b X) (fun σ r => σ r) π

theorem actual_relabeling_mean {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (X : ℝ)
    (hc : collisionEnergy b ≠ 0) (hp : primeEnergy b X ≠ 0) :
    uniformAverage (statistic b X) = 1 := by
  classical
  letI := pair_nonempty hb hbodd
  exact permutation_relabeling_mean_one _ _
    (collisionPairMass_sum hb hbodd hc) (primePairMass_sum hb hbodd X hp)

theorem actual_relabeling_variance {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (X : ℝ)
    (hc : collisionEnergy b ≠ 0) (hp : primeEnergy b X ≠ 0)
    (hk : 1 < Fintype.card (Pairs b)) :
    uniformVariance (statistic b X) =
      (Fintype.card (Pairs b) : ℝ) ^ 2 / (Fintype.card (Pairs b) - 1 : ℝ) *
        (∑ r, (centeredMass (collisionPairMass b) r) ^ 2) *
        (∑ r, (centeredMass (primePairMass b X) r) ^ 2) := by
  classical
  letI := pair_nonempty hb hbodd
  exact permutation_relabeling_variance _ _
    (collisionPairMass_sum hb hbodd hc) (primePairMass_sum hb hbodd X hp) hk

theorem base_three_statistic (X : ℝ) (hc : collisionEnergy 3 ≠ 0) (hp : primeEnergy 3 X ≠ 0)
    (π : Equiv.Perm (Pairs 3)) : statistic 3 X π = 1 := by
  classical
  letI := pair_nonempty (b := 3) (by decide) (by decide)
  exact permutation_relabeling_eq_one_of_card_one _ _
    (collisionPairMass_sum (by decide) (by decide) hc)
    (primePairMass_sum (by decide) (by decide) X hp) base_three_one_pair π

theorem base_three_overlap (X : ℝ) (hc : collisionEnergy 3 ≠ 0) (hp : primeEnergy 3 X ≠ 0) :
    scaledOverlap 3 X = 1 := by
  rw [scaledOverlap_pairs (by decide) (by decide)]
  exact base_three_statistic X hc hp (Equiv.refl _)

end NField.Alignment.SpectralActualRelabeling
