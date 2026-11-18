/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSampling
import Mathlib
/-! # Literal sampling and the forest/complement split

The finite split retains the same growing field and sampler in both sectors.
No estimate on either sector is assumed. The prime-square identity is reused
from the checked Common Reset development on the literal midpoint profile.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment
open CommonResetSampling CollisionRampEnergy CarrierJumpData DedekindReciprocity

def clockReading (N Q k : ℕ) : ℝ :=
  ((N/k : ℕ) : ℝ) *
    ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
      boundaryResponse N ((a : ℝ)/(k : ℝ)) *
        midpointRow Q ((a : ℝ)/(k : ℝ))

def selectedReading (N Q : ℕ) (mask : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, if mask k then clockReading N Q k else 0

theorem interior_eq_clock_sum (N Q : ℕ) :
    interiorSource N Q = ∑ k ∈ Finset.Icc 2 N, clockReading N Q k := rfl

theorem forest_complement_split (N Q : ℕ) (mask : ℕ → Bool) :
    interiorSource N Q = selectedReading N Q mask +
      selectedReading N Q (fun k => !(mask k)) := by
  unfold selectedReading
  rw [← Finset.sum_add_distrib, interior_eq_clock_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases hm : mask k <;> simp [hm]

/-- Exact arithmetic decomposition before an asymptotic forest estimate. -/
theorem prime_square_forest_decomposition {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (mask : ℕ → Bool) :
    defect (p-1) (p^2) - 1 =
      4*selectedReading (p-1) (p^2) (fun k => !(mask k))/(p : ℝ)^2 +
      (4*selectedReading (p-1) (p^2) mask/(p : ℝ)^2 -
        2/(p : ℝ) + 1/(p : ℝ)^2 -
        ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)) := by
  rw [prime_square_centered_identity hp hodd,
    forest_complement_split (p-1) (p^2) mask]
  ring

def rationalGridReading (N Q : ℕ) : ℚ :=
  (1/(Q : ℚ)) * ∑ a ∈ Finset.range Q, boundaryMidpoint N a Q ^ 2

/-- Every sample, including nonunits and the assigned origin, is retained. -/
theorem sampled_energy_rational (N : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    sampledEnergy N Q = (rationalGridReading N Q : ℝ) := by
  unfold sampledEnergy rationalGridReading
  simp_rw [boundaryResponse_rational hQ]
  push_cast
  rfl

/-- The exact continuous energy in the opening four-clock example. -/
theorem four_clock_continuous : continuousEnergy 4 = (23/9 : ℝ) := by
  rw [continuousEnergy, CommonResetGram.unweighted_gram]
  norm_num [show Finset.Icc 1 4 = {1,2,3,4} from by decide]

/-- The exact complete 25-point grid in the opening four-clock example. -/
theorem four_clock_grid : rationalGridReading 4 25 = (48/25 : ℚ) := by
  norm_num [rationalGridReading, boundaryMidpoint, rationalSawtooth,
    Finset.sum_range_succ]

theorem four_clock_sampled : sampledEnergy 4 25 = (48/25 : ℝ) := by
  rw [sampled_energy_rational 4 (by norm_num : 0 < 25), four_clock_grid]
  norm_num

/-- Restoring the actual origin square leaves precisely -1/225. -/
theorem four_clock_corrected_defect :
    continuousEnergy 4 - (sampledEnergy 4 25 + (4 : ℝ)^2/25) = -1/225 := by
  rw [four_clock_continuous, four_clock_sampled]
  norm_num

/-- The assigned midpoint origin is zero for every source cutoff. -/
theorem assigned_origin_zero (N : ℕ) : boundaryResponse N 0 = 0 := by
  simp [boundaryResponse, midpointRow]

end NField.ResetForests.Core
