/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.NormalizedRate
import NField.ResetForests.DyadicLoads
/-! # The uniform dyadic-band sufficient criterion on the actual packet source -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CostCriteria

open scoped BigOperators Topology
open Filter
open PrefixGeometry

def UniformBandCostSubpower
    (σ : ∀ p : OddPrime, ∀ j : ℕ, PacketPartition p.val (bandLoads p.val (2 ^ j))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in primeAtTop,
    ∀ j : ℕ, packetCost p (bandLoads p.val (2 ^ j)) (σ p j) ≤ C * primePower ε p

theorem uniform_band_normalized_readings
    (σ : ∀ p : OddPrime, ∀ j : ℕ, PacketPartition p.val (bandLoads p.val (2 ^ j)))
    (hσ : UniformBandCostSubpower σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in primeAtTop, ∀ j : ℕ,
      |packetReadout p.val (bandLoads p.val (2 ^ j)) / (p.val : ℝ) ^ 2| ≤
        C * primePower (-1 / 2 + ε) p := by
  obtain ⟨C, hC, hc⟩ := hσ (2 * ε) (by positivity)
  refine ⟨Real.sqrt (2 * C), by positivity, ?_⟩
  filter_upwards [hc, source_energy_eventual_budget] with p hp hE
  intro j
  have hpR : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  exact normalized_rate_bound hpR hC.le (packet_cost_nonnegative p _ (σ p j))
    (packet_readout_energy_cost_bound p _ (σ p j)) hE (hp j)

theorem band_normalized_readout_isBigO
    (σ : ∀ p : OddPrime, ∀ j : ℕ, PacketPartition p.val (bandLoads p.val (2 ^ j)))
    (hσ : UniformBandCostSubpower σ) (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsBigO primeAtTop
      (fun p => packetReadout p.val (entireLoads p.val) / (p.val : ℝ) ^ 2)
      (primePower (-1 / 2 + ε)) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨B, hB, hb⟩ := uniform_band_normalized_readings σ hσ δ hδ
  obtain ⟨A, hA, ha⟩ := band_count_small_power δ hδ
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨A * B, ?_⟩
  filter_upwards [hb] with p hp
  dsimp only [primePower] at hp ⊢
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hpR : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  have hs : packetReadout p.val (entireLoads p.val) / (p.val : ℝ) ^ 2 =
      ∑ j ∈ Finset.range (bandCount p.val),
        packetReadout p.val (bandLoads p.val (2 ^ j)) / (p.val : ℝ) ^ 2 := by
    rw [entire_readout_dyadic_sum, Finset.sum_div]
  rw [hs]
  calc
    _ ≤ ∑ j ∈ Finset.range (bandCount p.val),
        |packetReadout p.val (bandLoads p.val (2 ^ j)) / (p.val : ℝ) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (bandCount p.val), B * (p.val : ℝ) ^ (-1 / 2 + δ) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = (bandCount p.val : ℝ) * (B * (p.val : ℝ) ^ (-1 / 2 + δ)) := by simp
    _ ≤ (A * (p.val : ℝ) ^ δ) * (B * (p.val : ℝ) ^ (-1 / 2 + δ)) :=
      mul_le_mul_of_nonneg_right (ha p.val p.property.1.one_le) (by positivity)
    _ = (A * B) * ((p.val : ℝ) ^ δ * (p.val : ℝ) ^ (-1 / 2 + δ)) := by ring
    _ = (A * B) * (p.val : ℝ) ^ (δ + (-1 / 2 + δ)) := by
      rw [Real.rpow_add hpR δ (-1 / 2 + δ)]
    _ = _ := by congr 2; dsimp only [δ]; ring

theorem dyadic_band_half_power_criterion
    (σ : ∀ p : OddPrime, ∀ j : ℕ, PacketPartition p.val (bandLoads p.val (2 ^ j)))
    (hσ : UniformBandCostSubpower σ) : HalfPowerConclusion := by
  intro ε hε
  have h := (normalized_packet_fringe_isBigO ε hε).add (band_normalized_readout_isBigO σ hσ ε hε)
  simpa only [Pi.add_apply, sub_add_cancel] using h

theorem sufficient_half_power_criterion
    (σ : ∀ p : OddPrime, PacketPartition p.val (entireLoads p.val))
    (τ : ∀ p : OddPrime, ∀ j : ℕ, PacketPartition p.val (bandLoads p.val (2 ^ j))) :
    (EntireCostSubpower σ → HalfPowerConclusion) ∧
      (UniformBandCostSubpower τ → HalfPowerConclusion) :=
  ⟨entire_packet_half_power_criterion σ, dyadic_band_half_power_criterion τ⟩

end NField.ResetForests.CostCriteria
