/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.EndpointReciprocityBridge
import NField.Alignment.PrimitiveAdditiveConvolution

/-!
# Cyclic correlation reservoir

The jump-phase reservoir is regrouped by its actual cyclic prefix
correlations.  This supplies a finite, exact version of the manuscript's
correlation ladder: any pointwise correlation envelope transfers to a
sampling-defect envelope through the endpoint formula.
-/

namespace NField.Alignment.CyclicCorrelationReservoir

open scoped BigOperators
open NField.Alignment.BernoulliCurvature
open NField.Alignment.CarrierJumpData
open NField.Alignment.DedekindReciprocity
open NField.Alignment.EndpointReservoirAlias
open NField.Alignment.EndpointReciprocityBridge
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.PrimitiveAdditiveConvolution

/-- The manuscript's cyclic jump correlation `V_{k,s}(c)`. -/
noncomputable def cyclicCorrelation (k s c : ℕ) : ℚ :=
  if hk : 2 ≤ k then
    letI : NeZero k := ⟨by omega⟩
    ∑ u : (ZMod k)ˣ,
      cyclicPrefixResponse u.val.val k s *
        rationalSawtooth (c * u.val.val) k
  else 0

theorem primitive_sum_eq_cyclicCorrelation
    {k s c : ℕ} (hk : 2 ≤ k) :
    (∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k,
        cyclicPrefixResponse a k s * rationalSawtooth (c * a) k) =
      cyclicCorrelation k s c := by
  letI : NeZero k := ⟨by omega⟩
  letI : Fact (1 < k) := ⟨by omega⟩
  unfold cyclicCorrelation
  rw [dif_pos hk]
  have hreindex := (primitiveNatEquiv k hk).sum_comp
    (fun u : (ZMod k)ˣ =>
      cyclicPrefixResponse u.val.val k s *
        rationalSawtooth (c * u.val.val) k)
  rw [← hreindex]
  rw [Finset.sum_subtype
    ((Finset.Ico 1 k).filter fun a => a.Coprime k) (by intro; rfl)]
  apply Finset.sum_congr rfl
  intro a _ha
  simp [primitiveNatEquiv, ZMod.coe_unitOfCoprime,
    ZMod.val_natCast,
    Nat.mod_eq_of_lt
      (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]

/-- The endpoint jump reservoir is exactly the quotient-weighted sum of the
cyclic correlations. -/
theorem jumpPhaseReservoir_eq_cyclicCorrelations (p : ℕ) :
    jumpPhaseReservoir p =
      let N := p - 1
      ∑ k ∈ Finset.Icc 2 N,
        ((N / k : ℕ) : ℚ) * cyclicCorrelation k (N % k) (p ^ 2) := by
  unfold jumpPhaseReservoir
  dsimp only
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [primitive_sum_eq_cyclicCorrelation hk2]

/-- Absolute control of every cyclic correlation controls the complete jump
reservoir without discarding its quotient weights. -/
theorem abs_jumpPhaseReservoir_le
    (p : ℕ) (scale : ℕ → ℚ)
    (_hscale : ∀ k, 2 ≤ k → k ≤ p - 1 → 0 ≤ scale k)
    (hcorrelation : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤ scale k) :
    |jumpPhaseReservoir p| ≤
      ∑ k ∈ Finset.Icc 2 (p - 1),
        ((p - 1) / k : ℕ) * scale k := by
  rw [jumpPhaseReservoir_eq_cyclicCorrelations]
  calc
    |∑ k ∈ Finset.Icc 2 (p - 1),
        (((p - 1) / k : ℕ) : ℚ) *
          cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤
        ∑ k ∈ Finset.Icc 2 (p - 1),
          |(((p - 1) / k : ℕ) : ℚ) *
            cyclicCorrelation k ((p - 1) % k) (p ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 2 (p - 1),
        ((p - 1) / k : ℕ) * scale k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      rw [abs_mul, abs_of_nonneg (by positivity :
        (0 : ℚ) ≤ (((p - 1) / k : ℕ) : ℚ))]
      gcongr
      exact hcorrelation k hkI.1 hkI.2

/-- The exact finite envelope transferred from cyclic correlations to the
sampling defect. -/
noncomputable def cyclicSamplingEnvelope
    (p : ℕ) (scale : ℕ → ℚ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
    4 / (p : ℝ) ^ 2 *
      (((∑ k ∈ Finset.Icc 2 (p - 1),
        (((p - 1) / k : ℕ) : ℚ) * scale k : ℚ) : ℚ) : ℝ) +
    2 * (boundarySlope p : ℝ) /
      (p : ℝ) ^ 4 * |((carrierBernoulliCurvature p : ℚ) : ℝ)|

/-- One rung of the cyclic-correlation ladder on the actual sampling defect. -/
theorem samplingDefect_le_of_cyclicCorrelation
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (scale : ℕ → ℚ)
    (hscale : ∀ k, 2 ≤ k → k ≤ p - 1 → 0 ≤ scale k)
    (hcorrelation : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤ scale k) :
    |samplingDefect hp| ≤ cyclicSamplingEnvelope p scale := by
  have hA := abs_jumpPhaseReservoir_le p scale hscale hcorrelation
  have hformula :=
    EndpointReciprocityBridge.exact_endpoint_reservoir_alias_formula hp hpodd
  rw [hformula]
  calc
    |((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 -
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4| ≤
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        4 / (p : ℝ) ^ 2 * |((jumpPhaseReservoir p : ℚ) : ℝ)| +
        2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4 *
          |((carrierBernoulliCurvature p : ℚ) : ℝ)| := by
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
      have hN : 0 ≤ ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 := by positivity
      have hL : 0 ≤ (boundarySlope p : ℝ) := by
        unfold boundarySlope
        positivity
      rw [show
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 =
          (4 / (p : ℝ) ^ 2) * (jumpPhaseReservoir p : ℝ) by ring,
        show
          2 * (boundarySlope p : ℝ) *
              (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 =
            (2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4) *
              (carrierBernoulliCurvature p : ℝ) by ring]
      calc
        |((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
              (4 / (p : ℝ) ^ 2) * (jumpPhaseReservoir p : ℝ) -
              (2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4) *
                (carrierBernoulliCurvature p : ℝ)| ≤
            |((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2| +
              |(4 / (p : ℝ) ^ 2) * (jumpPhaseReservoir p : ℝ)| +
              |(2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4) *
                (carrierBernoulliCurvature p : ℝ)| := by
          let x := ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2
          let y := (4 / (p : ℝ) ^ 2) * (jumpPhaseReservoir p : ℝ)
          let z := (2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4) *
            (carrierBernoulliCurvature p : ℝ)
          change |x + y - z| ≤ |x| + |y| + |z|
          have hxy := add_le_add_right (abs_add_le x y) |z|
          have hxy' : |x + y| + |z| ≤ |x| + |y| + |z| := by
            simpa [add_comm, add_left_comm, add_assoc] using hxy
          exact (abs_sub (x + y) z).trans hxy'
        _ = _ := by
          rw [abs_of_nonneg hN, abs_mul, abs_mul]
          have h4 : 0 ≤ 4 / (p : ℝ) ^ 2 := by positivity
          have h2L : 0 ≤ 2 * (boundarySlope p : ℝ) / (p : ℝ) ^ 4 := by
            exact div_nonneg (mul_nonneg (by norm_num) hL) (by positivity)
          rw [abs_of_nonneg h4, abs_of_nonneg h2L]
    _ ≤ cyclicSamplingEnvelope p scale := by
      unfold cyclicSamplingEnvelope
      gcongr
      exact_mod_cast hA

/-- The manuscript's three finite rungs, with square-harmonic, harmonic, and
constant cyclic-correlation envelopes respectively. -/
theorem cyclic_correlation_ladder
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hquadratic : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤
        k * harmonic k ^ 2)
    (hlinear : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤
        k * harmonic k)
    (hbounded : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤ k) :
    |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k * harmonic k ^ 2) ∧
      |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k * harmonic k) ∧
      |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k) := by
  refine ⟨samplingDefect_le_of_cyclicCorrelation hp hpodd _ ?_ hquadratic,
    samplingDefect_le_of_cyclicCorrelation hp hpodd _ ?_ hlinear,
    samplingDefect_le_of_cyclicCorrelation hp hpodd _ ?_ hbounded⟩
  · intro k _hk _hkp
    exact mul_nonneg (by positivity) (by
      unfold harmonic
      positivity)
  · intro k _hk _hkp
    exact mul_nonneg (by positivity) (by
      unfold harmonic
      positivity)
  · intro k _hk _hkp
    positivity

end NField.Alignment.CyclicCorrelationReservoir
