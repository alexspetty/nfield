/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerSingularity
import NField.Alignment.CollisionJordanVariance

/-!
# Exact finite enclosures for full collision amplitudes

An omitted conductor subseries is bounded by the actual omitted unit mass.
The resulting endpoints use finite rational collision weights only. This
enclosure does not claim the sharper conductor-dependent tail estimate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeEnclosure

open scoped BigOperators Classical
open Filter CollisionRemainderDynamics CollisionMassReadout
open CollisionJordanVariance CollisionIntegerSingularity

def omittedAmplitude (q M : ℕ) : ℝ :=
  ∑' j : ℕ, if q ∣ j+(M+1) then collisionWeight (j+(M+1)) else 0

theorem omittedAmplitude_summable (q M : ℕ) :
    Summable (fun j : ℕ => if q ∣ j+(M+1) then collisionWeight (j+(M+1)) else 0) :=
  (amplitude_summable q).comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem amplitude_cutoff_split (q M : ℕ) :
    amplitude q = finiteAmplitude collisionWeight q M + omittedAmplitude q M := by
  have h := (amplitude_summable q).sum_add_tsum_nat_add (M+1)
  rw [sum_range_zero_one _ (by simp) (by simp)] at h
  exact h.symm

theorem omittedAmplitude_nonneg (q M : ℕ) : 0 ≤ omittedAmplitude q M := by
  apply tsum_nonneg
  intro j
  split_ifs <;> simp [collisionWeight_nonneg]

theorem omittedAmplitude_le_tailMass (q M : ℕ) :
    omittedAmplitude q M ≤ tailMass M := by
  apply (omittedAmplitude_summable q M).tsum_le_tsum _
    (collisionWeight_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h))
  intro j
  split_ifs <;> simp [collisionWeight_nonneg]

theorem tailMass_eq_complement (M : ℕ) :
    tailMass M = 1-∑ k ∈ Finset.Icc 2 M, collisionWeight k := by
  have h := collisionWeight_summable.sum_add_tsum_nat_add (M+1)
  rw [collisionWeight_tsum, sum_range_weights] at h
  change (∑ k ∈ Finset.Icc 2 M, collisionWeight k)+tailMass M=1 at h
  linarith

def amplitudeUpper (q M : ℕ) : ℝ :=
  finiteAmplitude collisionWeight q M+(1-∑ k ∈ Finset.Icc 2 M, collisionWeight k)

theorem amplitude_mem_enclosure (q M : ℕ) :
    amplitude q ∈ Set.Icc (finiteAmplitude collisionWeight q M) (amplitudeUpper q M) := by
  constructor
  · exact finiteAmplitude_le_amplitude q M
  · rw [amplitude_cutoff_split q M, amplitudeUpper]
    exact add_le_add_right (by simpa [tailMass_eq_complement] using
      omittedAmplitude_le_tailMass q M) _

theorem amplitude_enclosure_width (q M : ℕ) :
    amplitudeUpper q M-finiteAmplitude collisionWeight q M=tailMass M := by
  rw [amplitudeUpper, tailMass_eq_complement]
  ring

theorem amplitude_enclosure_width_tendsto (q : ℕ) :
    Tendsto (fun M => amplitudeUpper q M-finiteAmplitude collisionWeight q M)
      atTop (nhds 0) := by
  simpa only [amplitude_enclosure_width] using tailMass_tendsto_zero

theorem amplitudeUpper_tendsto (q : ℕ) :
    Tendsto (amplitudeUpper q) atTop (nhds (amplitude q)) := by
  have h := (finiteAmplitude_tendsto q).add tailMass_tendsto_zero
  change Tendsto (fun M => finiteAmplitude collisionWeight q M+
    (1-∑ k ∈ Finset.Icc 2 M, collisionWeight k)) atTop (nhds (amplitude q))
  simpa only [add_zero, amplitudeUpper, tailMass_eq_complement] using h

end NField.Alignment.CollisionAmplitudeEnclosure
