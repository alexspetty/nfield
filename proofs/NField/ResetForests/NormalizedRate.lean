/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketCost
/-! # The epsilon-rescaled rate implication in the original p-square units -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CostCriteria

open scoped BigOperators Topology
open Filter
open NField.Alignment

def primePower (a : ℝ) (p : OddPrime) : ℝ := (p.val : ℝ) ^ a

def sampleError (p : OddPrime) : ℝ := CommonResetSampling.defect (p.val - 1) (p.val ^ 2) - 1

def HalfPowerConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO primeAtTop sampleError (primePower (-1 / 2 + ε))

def EntireCostSubpower (σ : ∀ p : OddPrime, PacketPartition p.val (entireLoads p.val)) : Prop :=
  ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO primeAtTop
    (fun p => packetCost p (entireLoads p.val) (σ p)) (primePower ε)

theorem positive_bigO_bound (f : OddPrime → ℝ) (a : ℝ)
    (hf : Asymptotics.IsBigO primeAtTop f (primePower a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in primeAtTop, |f p| ≤ C * primePower a p := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hf
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [hC] with p hp
  have hpow : 0 ≤ primePower a p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [Real.norm_eq_abs, abs_of_nonneg hpow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hpow)

theorem normalized_rate_bound {x E R D C ε : ℝ} (hx : 0 < x) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hD : |D| ^ 2 ≤ E * R) (hE : E ≤ 2 * x ^ 3) (hc : R ≤ C * x ^ (2 * ε)) :
    |D / x ^ 2| ≤ Real.sqrt (2 * C) * x ^ (-1 / 2 + ε) := by
  let a : ℝ := -1 / 2 + ε
  have hsq : (x ^ a) ^ 2 = x ^ (a + a) := by
    rw [Real.rpow_add hx a a, pow_two]
  have hs : (x ^ a) ^ 2 * x ^ 4 = x ^ 3 * x ^ (2 * ε) := by
    calc
      _ = x ^ (a + a) * x ^ (4 : ℝ) :=
        congrArg₂ (fun u v : ℝ => u * v) hsq (Real.rpow_natCast x 4).symm
      _ = x ^ (a + a + 4) := (Real.rpow_add hx (a + a) 4).symm
      _ = x ^ ((3 : ℝ) + 2 * ε) := by congr 1; dsimp only [a]; ring
      _ = _ := (Real.rpow_add hx 3 (2 * ε)).trans
        (congrArg (fun u : ℝ => u * x ^ (2 * ε)) (Real.rpow_natCast x 3))
  have hB : (Real.sqrt (2 * C) * x ^ a) ^ 2 * x ^ 4 =
      (2 * x ^ 3) * (C * x ^ (2 * ε)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ = (2 * C) * ((x ^ a) ^ 2 * x ^ 4) := by ring
      _ = _ := by rw [hs]; ring
  have hD' : D ^ 2 ≤ E * R := by simpa only [sq_abs] using hD
  have hb : D ^ 2 ≤ (2 * x ^ 3) * (C * x ^ (2 * ε)) :=
    hD'.trans (mul_le_mul hE hc hR (by positivity))
  have hd : |D / x ^ 2| ^ 2 ≤ (Real.sqrt (2 * C) * x ^ a) ^ 2 := by
    rw [sq_abs, div_pow]
    apply (div_le_iff₀ (by positivity : 0 < (x ^ 2) ^ 2)).mpr
    rw [show (x ^ 2) ^ 2 = x ^ 4 by ring]
    exact hb.trans_eq hB.symm
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx.le _))).mp hd

theorem entire_normalized_readout_isBigO
    (σ : ∀ p : OddPrime, PacketPartition p.val (entireLoads p.val)) (hσ : EntireCostSubpower σ)
    (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsBigO primeAtTop
      (fun p => packetReadout p.val (entireLoads p.val) / (p.val : ℝ) ^ 2)
      (primePower (-1 / 2 + ε)) := by
  obtain ⟨C, hC, hc⟩ := positive_bigO_bound _ _ (hσ (2 * ε) (by positivity))
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨Real.sqrt (2 * C), ?_⟩
  filter_upwards [hc, source_energy_eventual_budget] with p hp hE
  dsimp only [primePower] at hp ⊢
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hpR : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  exact normalized_rate_bound hpR hC.le (packet_cost_nonnegative p _ (σ p))
    (packet_readout_energy_cost_bound p _ (σ p)) hE ((le_abs_self _).trans hp)

theorem normalized_packet_fringe_isBigO (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsBigO primeAtTop
      (fun p => sampleError p - packetReadout p.val (entireLoads p.val) / (p.val : ℝ) ^ 2)
      (primePower (-1 / 2 + ε)) := by
  obtain ⟨C, _, hC⟩ := CompletePackets.complete_packet_reading_half_power ε hε
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Eventually.of_forall ?_⟩
  intro p
  dsimp only [primePower]
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hp := hC p.val p.property.1 p.property.2
  rw [entire_readout_packet_sum]
  change |CommonResetSampling.defect (p.val - 1) (p.val ^ 2) - 1 -
    CompletePackets.packetSignedSum p.val / (p.val : ℝ) ^ 2| ≤ _
  have he : (1 / (p.val : ℝ) ^ 2) * CompletePackets.packetSignedSum p.val =
      CompletePackets.packetSignedSum p.val / (p.val : ℝ) ^ 2 := by ring
  simpa only [he] using hp

theorem entire_packet_half_power_criterion
    (σ : ∀ p : OddPrime, PacketPartition p.val (entireLoads p.val))
    (hσ : EntireCostSubpower σ) : HalfPowerConclusion := by
  intro ε hε
  have h := (normalized_packet_fringe_isBigO ε hε).add (entire_normalized_readout_isBigO σ hσ ε hε)
  simpa only [Pi.add_apply, sub_add_cancel] using h

end NField.ResetForests.CostCriteria
