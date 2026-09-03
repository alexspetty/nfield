/-
Author: Alexander S. Petty
-/

import NField.Alignment.BernoulliCurvature
import NField.Alignment.CarrierJumpData
import NField.Alignment.ExactSamplingReservoirBridge

/-!
# Endpoint and jump-phase reservoir

The finite jump-phase and curvature reservoirs from the carrier-grid alias
formula.  The Fourier/Abel alias identity is isolated as a proposition on the
actual sampled and continuous energies; once supplied, the endpoint formula
is derived here with no additional algebraic assumption.
-/

namespace NField.Alignment.EndpointReservoirAlias

open scoped BigOperators
open NField.Alignment.BernoulliCurvature
open NField.Alignment.CarrierJumpData
open NField.Alignment.CollisionBernoulliStraightening
open NField.Alignment.DedekindReciprocity
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.SecondaryCapacityLedger

/-- The signed jump-phase correlation `A_p` in exact rational arithmetic. -/
noncomputable def jumpPhaseReservoir (p : ℕ) : ℚ :=
  let N := p - 1
  ∑ k ∈ Finset.Icc 2 N,
    ((N / k : ℕ) : ℚ) *
      ∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k,
        cyclicPrefixResponse a k (N % k) *
          rationalSawtooth ((p ^ 2) * a) k

/-- The common classical slope of the straightened Bernoulli boundary. -/
def boundarySlope (p : ℕ) : ℚ := (p * (p - 1) : ℕ)

/-- The unsimplified sum of value jumps against the first periodic Bernoulli
function.  This is the literal finite term produced by the symmetric Abel
limit before it is named as the jump-phase reservoir. -/
noncomputable def rawValueJumpSum (p : ℕ) : ℚ :=
  let N := p - 1
  ∑ k ∈ Finset.Icc 2 N,
    -4 * ((N / k : ℕ) : ℚ) *
      ∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k,
        cyclicPrefixResponse a k (N % k) *
          rationalSawtooth ((p ^ 2) * a) k

/-- The origin and nonzero derivative jumps against the second periodic
Bernoulli function, still in the raw form delivered by Fourier inversion. -/
noncomputable def rawSlopeJumpSum (p : ℕ) : ℚ :=
  let N := p - 1
  let L := boundarySlope p
  (-4 * L * (N : ℚ)) * (1 / 6 : ℚ) +
    ∑ k ∈ Finset.Icc 2 N,
      (-4 * L * ((N / k : ℕ) : ℚ)) *
        multipliedReducedBernoulliTwoSum (p ^ 2) k

/-- The source-level periodic Fourier/Abel identity, before any manuscript
reservoir is substituted.  This is the analytic boundary: the regulated
origin, the value jumps, and the derivative jumps remain visibly separate. -/
def PeriodicJumpFourierAbelIdentity
    {p : ℕ} (hp : p.Prime) : Prop :=
  bernoulliEnergy hp / (p : ℝ) ^ 2 - continuousCapacity (p - 1) =
    -(((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) +
      (rawValueJumpSum p : ℝ) / (p : ℝ) ^ 2 -
      (rawSlopeJumpSum p : ℝ) / (2 * (p : ℝ) ^ 4)

theorem rawValueJumpSum_eq (p : ℕ) :
    rawValueJumpSum p = -4 * jumpPhaseReservoir p := by
  unfold rawValueJumpSum jumpPhaseReservoir
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

theorem rawSlopeJumpSum_eq (p : ℕ) :
    rawSlopeJumpSum p =
      -4 * boundarySlope p * carrierBernoulliCurvature p := by
  unfold rawSlopeJumpSum carrierBernoulliCurvature
  dsimp only
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _hk
    ring

/-- Inserting the exact finite jump ledgers into the raw Fourier/Abel identity
gives the manuscript's reservoir form. -/
theorem periodic_jump_aliasing
    {p : ℕ} (hp : p.Prime)
    (hfourierAbel : PeriodicJumpFourierAbelIdentity hp) :
    bernoulliEnergy hp / (p : ℝ) ^ 2 - continuousCapacity (p - 1) =
      -(((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) -
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 +
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 := by
  unfold PeriodicJumpFourierAbelIdentity at hfourierAbel
  rw [rawValueJumpSum_eq, rawSlopeJumpSum_eq] at hfourierAbel
  push_cast at hfourierAbel
  convert hfourierAbel using 1
  all_goals ring

/-- The actual endpoint-reservoir alias formula follows from the periodic
jump certificate and the already proved collision-to-Bernoulli energy
identity. -/
theorem exact_endpoint_reservoir_alias_formula
    {p : ℕ} (hp : p.Prime)
    (hfourierAbel : PeriodicJumpFourierAbelIdentity hp) :
    samplingDefect hp =
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 -
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 := by
  have halias := periodic_jump_aliasing hp hfourierAbel
  unfold samplingDefect
  rw [collision_energy_eq_bernoulli_energy hp]
  linear_combination -halias

end NField.Alignment.EndpointReservoirAlias
