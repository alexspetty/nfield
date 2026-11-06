/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetGrid
import NField.Alignment.CommonResetGram
import NField.Alignment.EndpointReciprocityBridge

/-! # The published prime-square sampling identity

The integral and samples are the literal real midpoint profile. The interior
source retains every reduced reset, its full clock multiplicity and the
actual prime-square multiplier.
-/

noncomputable section

namespace NField.Alignment.CommonResetSampling

open scoped BigOperators
open CollisionRampEnergy CommonResetGrid CarrierJumpData DedekindReciprocity
open EndpointReservoirAlias

def continuousEnergy (N : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, boundaryResponse N x ^ 2

def sampledEnergy (N q : ℕ) : ℝ :=
  (1/(q : ℝ)) * ∑ a ∈ Finset.range q, boundaryResponse N ((a : ℝ)/(q : ℝ)) ^ 2

def defect (N q : ℕ) : ℝ := continuousEnergy N - sampledEnergy N q

def interiorSource (N q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, ((N/d : ℕ) : ℝ) *
    ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      boundaryResponse N ((a : ℝ)/(d : ℝ)) * midpointRow q ((a : ℝ)/(d : ℝ))

/-- Title: `The real reset reading equals its rational clock sum`. -/
theorem boundaryResponse_rational {d : ℕ} (hd : 0 < d) (N a : ℕ) :
    boundaryResponse N ((a : ℝ)/(d : ℝ)) = (boundaryMidpoint N a d : ℝ) := by
  unfold boundaryResponse boundaryMidpoint
  push_cast
  congr 1
  have hsets : Finset.Icc 1 N = Finset.Ico 1 (N+1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.add_comm] using midpointRow_rational hd (j+1) a

/-- Title: `Complete clock cycles leave the exact terminal prefix`. -/
theorem boundaryResponse_reduced_prefix {d a : ℕ} (hd : 0 < d) (ha : a.Coprime d)
    (N : ℕ) :
    boundaryResponse N ((a : ℝ)/(d : ℝ)) = (cyclicPrefixResponse a d (N%d) : ℝ) := by
  rw [boundaryResponse_rational hd, boundaryMidpoint_eq_cyclicPrefix hd ha]

/-- Title: `The interior source is the complete rational reset reservoir`. -/
theorem interiorSource_prime (p : ℕ) :
    interiorSource (p-1) (p^2) = (jumpPhaseReservoir p : ℝ) := by
  unfold interiorSource jumpPhaseReservoir
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hdpos : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  rw [boundaryResponse_reduced_prefix hdpos (Finset.mem_filter.mp ha).2,
    midpointRow_rational hdpos]

/-- Title: `The finite carry table gives the literal sampled energy`. -/
theorem sampledEnergy_prime {p : ℕ} (hp : p.Prime) :
    sampledEnergy (p-1) (p^2) =
      CollisionBernoulliStraightening.collisionEnergy hp / (p : ℝ)^2 := by
  unfold sampledEnergy
  simp only [Nat.cast_pow]
  rw [← carry_energy_representation hp.two_le, carryEnergy_eq_complex hp.two_le]
  have he : CommonResetCarry.collisionEnergy hp.two_le =
      CollisionBernoulliStraightening.collisionEnergy hp := rfl
  rw [he]
  ring

theorem defect_prime_eq_existing {p : ℕ} (hp : p.Prime) :
    defect (p-1) (p^2) = ExactSamplingReservoirBridge.samplingDefect hp := by
  rw [defect, continuousEnergy, boundaryResponse_energy, sampledEnergy_prime hp]
  rfl

/-- Title: `The prime-square defect separates the common reset and interior source`. -/
theorem prime_square_sampling_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    defect (p-1) (p^2) =
      ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2 +
      4*interiorSource (p-1) (p^2)/(p : ℝ)^2 -
      ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) := by
  rw [defect_prime_eq_existing hp, interiorSource_prime,
    EndpointReciprocityBridge.exact_endpoint_reservoir_alias_formula hp hodd,
    EndpointReciprocityBridge.carrierBernoulliCurvature_eq_harmonic hp]
  unfold boundarySlope
  push_cast
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

/-- Title: `The unit-defect remainder has its exact signed source formula`. -/
theorem prime_square_centered_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    defect (p-1) (p^2) - 1 =
      4*interiorSource (p-1) (p^2)/(p : ℝ)^2 - 2/(p : ℝ) + 1/(p : ℝ)^2 -
      ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) := by
  rw [prime_square_sampling_identity hp hodd]
  push_cast [Nat.cast_sub hp.one_le]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

/-- Title: `Correcting the origin removes exactly the common reset square`. -/
theorem corrected_grid_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    continuousEnergy (p-1) -
      (sampledEnergy (p-1) (p^2) + ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2) =
      4*interiorSource (p-1) (p^2)/(p : ℝ)^2 -
      ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) := by
  have h := prime_square_sampling_identity hp hodd
  unfold defect at h
  linarith

end NField.Alignment.CommonResetSampling
