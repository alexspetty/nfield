/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.ResetForests.DivisorBudget
import NField.ResetForests.Sampling
import NField.ResetForests.OrderedWork
import NField.ResetForests.Words
import NField.ResetForests.Carry
import NField.ResetForests.Readout
import NField.ResetForests.CoherentWork
import NField.ResetForests.Targets
import NField.ResetForests.GridWork
import NField.ResetForests.Centered
import NField.ResetForests.CarryClock
import NField.ResetForests.ClockBinary
import NField.ResetForests.PhaseFringe
import NField.ResetForests.LoadTail
import NField.ResetForests.ForestRates
import NField.ResetForests.Opening
import NField.ResetForests.Complement
import NField.ResetForests.WindowExample
import NField.ResetForests.EnergyMatrices
import NField.ResetForests.FibreDirections
import NField.ResetForests.FibreBasisTrace
import NField.ResetForests.GramSectors
import NField.ResetForests.TorusIncidence
import NField.ResetForests.CompleteReset
import NField.ResetForests.OrderedMasks
import NField.ResetForests.PacketPopulation
import NField.ResetForests.PacketReading
/-! # Both directions of the complete signed-packet bound

The uniform remainder has the same half-power exponent as the target.
The original odd-prime quantifiers and every epsilon are retained.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketCycles

open SignedForestWork CompletePackets NField.Alignment

theorem unscaled_half_rate_iff (f g : ℕ → ℝ)
    (hr : PrimePowerRate (fun p => f p - g p / (p : ℝ) ^ 2) (-1 / 2)) :
    PrimePowerRate f (-1 / 2) ↔ PrimePowerRate g (3 / 2) := by
  constructor
  · intro hf ε hε
    obtain ⟨F, hF, hf⟩ := hf ε hε
    obtain ⟨D, hD, hd⟩ := hr ε hε
    refine ⟨F + D, by positivity, ?_⟩
    intro p hp hodd
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have htri : |g p / (p : ℝ) ^ 2| ≤ (F + D) * (p : ℝ) ^ (-1 / 2 + ε) := by
      calc
        _ = |f p - (f p - g p / (p : ℝ) ^ 2)| := by congr 1; ring
        _ ≤ |f p| + |f p - g p / (p : ℝ) ^ 2| := by
          calc
            _ = |f p + -(f p - g p / (p : ℝ) ^ 2)| := rfl
            _ ≤ |f p| + |-(f p - g p / (p : ℝ) ^ 2)| := abs_add_le _ _
            _ = _ := by rw [abs_neg]
        _ ≤ F * (p : ℝ) ^ (-1 / 2 + ε) + D * (p : ℝ) ^ (-1 / 2 + ε) :=
          add_le_add (hf p hp hodd) (hd p hp hodd)
        _ = _ := by ring
    calc
      |g p| = (p : ℝ) ^ 2 * |g p / (p : ℝ) ^ 2| := by
        rw [abs_div, abs_of_nonneg (sq_nonneg (p : ℝ))]
        field_simp
      _ ≤ (p : ℝ) ^ 2 * ((F + D) * (p : ℝ) ^ (-1 / 2 + ε)) :=
        mul_le_mul_of_nonneg_left htri (sq_nonneg _)
      _ = (F + D) * ((p : ℝ) ^ 2 * (p : ℝ) ^ (-1 / 2 + ε)) := by ring
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_add hpR]
        congr 2
        ring
  · intro hg ε hε
    obtain ⟨G, hG, hg⟩ := hg ε hε
    obtain ⟨D, hD, hd⟩ := hr ε hε
    refine ⟨D + G, by positivity, ?_⟩
    intro p hp hodd
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hnorm : |g p / (p : ℝ) ^ 2| ≤ G * (p : ℝ) ^ (-1 / 2 + ε) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (p : ℝ))]
      calc
        _ ≤ (G * (p : ℝ) ^ (3 / 2 + ε)) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (hg p hp hodd) (sq_nonneg _)
        _ = _ := by
          rw [mul_div_assoc, ← Real.rpow_two, ← Real.rpow_sub hpR]
          congr 2
          ring
    calc
      |f p| = |(f p - g p / (p : ℝ) ^ 2) + g p / (p : ℝ) ^ 2| := by congr 1; ring
      _ ≤ |f p - g p / (p : ℝ) ^ 2| + |g p / (p : ℝ) ^ 2| := abs_add_le _ _
      _ ≤ D * (p : ℝ) ^ (-1 / 2 + ε) + G * (p : ℝ) ^ (-1 / 2 + ε) :=
        add_le_add (hd p hp hodd) hnorm
      _ = _ := by ring

theorem complete_packet_half_rate_iff :
    PrimePowerRate centeredSamplingDefect (-1 / 2) ↔
      PrimePowerRate packetSignedSum (3 / 2) := by
  apply unscaled_half_rate_iff
  intro ε hε
  obtain ⟨C, hC, hc⟩ := complete_packet_reading_half_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  have h := hc p hp hodd
  simpa only [centeredSamplingDefect, one_div_mul_eq_div] using h

end NField.ResetForests.PacketCycles
