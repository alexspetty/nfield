/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialSpectralMoments

/-! # Every nonzero rational frequency has positive mass -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralSupport

open scoped BigOperators
open MeasureTheory CollisionSpectralWeights CollisionAtomicSpectra CollisionJordanVariance
open CollisionRemainderDynamics CollisionCosecantIdentity CollisionPrimitiveFourier
open DedekindFourierMoment

theorem amplitude_pos {q : ℕ} (hq : 2 ≤ q) : 0 < amplitude q := by
  have ht := (amplitude_summable q).le_tsum q
    (fun k _ => show 0 ≤ (if q ∣ k then collisionWeight k else 0) by
      split_ifs <;> simp [collisionWeight_nonneg])
  simp only [dvd_refl, if_true] at ht
  exact (collisionWeight_pos hq).trans_le ht

theorem incrementMass_pos (i : SpectralAddress) : 0 < incrementMass i := by
  have ha := amplitude_pos (address_period i)
  unfold incrementMass
  positivity

theorem potentialMass_pos (i : SpectralAddress) : 0 < potentialMass i := by
  apply mul_pos (incrementMass_pos i)
  unfold chordEnergy
  apply inv_pos.mpr
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (negativeRoot_primitive_ne_one (address_period i) (address_coprime i)).symm))

theorem atomicMeasure_atom_lower (w : SpectralAddress → ℝ) (i : SpectralAddress) :
    ENNReal.ofReal (w i) ≤ atomicMeasure w {frequency i} := by
  have h := Measure.le_sum
    (fun j => ENNReal.ofReal (w j) • Measure.dirac (frequency j)) i
  have hs := h (s := {frequency i})
  simpa only [atomicMeasure, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _),
    smul_eq_mul, mul_one] using hs

theorem incrementMeasure_atom_pos (i : SpectralAddress) :
    0 < incrementMeasure {frequency i} :=
  (ENNReal.ofReal_pos.mpr (incrementMass_pos i)).trans_le (atomicMeasure_atom_lower _ i)

theorem potentialMeasure_atom_pos (i : SpectralAddress) :
    0 < potentialMeasure {frequency i} :=
  (ENNReal.ofReal_pos.mpr (potentialMass_pos i)).trans_le (atomicMeasure_atom_lower _ i)

end NField.Alignment.CollisionSpectralSupport
