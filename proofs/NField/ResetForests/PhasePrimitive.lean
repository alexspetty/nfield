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
import NField.ResetForests.PacketPeriod
import NField.ResetForests.StripTransport
import NField.ResetForests.RecordSignature
import NField.ResetForests.ActualRecord
import NField.ResetForests.SeedResponse
import NField.ResetForests.ActualPrefixCost
import NField.ResetForests.DyadicPrefixes
import NField.ResetForests.BandCriterion
import NField.ResetForests.EuclideanExamples
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
/-! # The actual integrated source and its mean

The integral retains the midpoint field. Its one-sided derivatives use the
corresponding one-sided traces, including every rational contact.
-/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ShiftedEnergy

open scoped BigOperators Topology
open Filter Set MeasureTheory NField.Alignment
open CommonResetGram CollisionRampEnergy RealSawtoothDistribution
open SourceMetrics FibreReconstruction FibreTraces

def sourcePrimitive (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, weightedProfile N c t

def reciprocalMoment (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j/(j : ℝ)

theorem profile_integrable (N : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (weightedProfile N c) volume a b := by
  unfold weightedProfile
  simpa only [Finset.sum_apply] using (IntervalIntegrable.sum (Finset.Icc 1 N) (fun j hj =>
    (midpointRow_intervalIntegrable (Finset.mem_Icc.mp hj).1 a b).const_mul (c j))).const_mul 2

theorem profile_measurable (N : ℕ) (c : ℕ → ℝ) :
    Measurable (weightedProfile N c) := by
  unfold weightedProfile
  exact (Finset.measurable_sum _ (fun j _ =>
    (sawtooth_measurable.comp (measurable_const.mul measurable_id)).const_mul (c j))).const_mul 2

theorem contact_ae_zero (N : ℕ) (c : ℕ → ℝ) :
    contactMass N c =ᵐ[volume] fun _ => 0 := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      ∀ᵐ x ∂volume, Int.fract ((j : ℝ)*x) ≠ 0 := by
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show 0<j from (Finset.mem_Icc.mp hj).1).ne'
    filter_upwards [(Set.countable_range (fun z : ℤ => (z : ℝ)/(j : ℝ))).ae_notMem volume]
      with x hx
    intro hz
    obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hz
    apply hx
    refine ⟨z, ?_⟩
    dsimp only
    rw [hz]
    field_simp
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hterm j))] with x hx
  exact Finset.sum_eq_zero (fun j hj => if_neg (hx j hj))

theorem right_profile_ae (N : ℕ) (c : ℕ → ℝ) :
    profileRight N c =ᵐ[volume] weightedProfile N c := by
  filter_upwards [contact_ae_zero N c] with x hx
  simp only [profileRight, hx, sub_zero]

theorem right_profile_integrable (N : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (profileRight N c) volume a b :=
  (profile_integrable N c a b).congr_ae (ae_restrict_of_ae (right_profile_ae N c).symm)

theorem profile_mean_zero (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, weightedProfile N c x)=0 := by
  unfold weightedProfile
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun j hj => (midpointRow_intervalIntegrable (Finset.mem_Icc.mp hj).1 0 1).const_mul (c j))]
  simp only [intervalIntegral.integral_const_mul]
  have hz : (∑ j ∈ Finset.Icc 1 N, c j*∫ x in (0 : ℝ)..1, midpointRow j x)=0 :=
    Finset.sum_eq_zero (fun j hj => by rw [midpointRow_mean_zero (Finset.mem_Icc.mp hj).1, mul_zero])
  rw [hz, mul_zero]

theorem primitive_zero (N : ℕ) (c : ℕ → ℝ) : sourcePrimitive N c 0=0 := by
  simp [sourcePrimitive]

theorem primitive_one (N : ℕ) (c : ℕ → ℝ) : sourcePrimitive N c 1=0 :=
  profile_mean_zero N c

theorem primitive_continuous (N : ℕ) (c : ℕ → ℝ) :
    Continuous (sourcePrimitive N c) :=
  intervalIntegral.continuous_primitive (profile_integrable N c) 0

theorem primitive_right_derivative (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (sourcePrimitive N c) (profileRight N c x) (Ioi x) x := by
  have h : HasDerivWithinAt (sourcePrimitive N c) (profileRight N c x) (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
      (profile_integrable N c 0 x)
      (profile_measurable N c).stronglyMeasurable.stronglyMeasurableAtFilter
      ((weighted_profile_right_limit N c x).mono_left inf_le_left)
  exact h.mono Ioi_subset_Ici_self

theorem primitive_left_derivative (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (sourcePrimitive N c) (profileLeft N c x) (Iio x) x := by
  have h : HasDerivWithinAt (sourcePrimitive N c) (profileLeft N c x) (Iic x) x :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
      (profile_integrable N c 0 x)
      (profile_measurable N c).stronglyMeasurable.stronglyMeasurableAtFilter
      (show Tendsto (weightedProfile N c) (𝓝[≤] x ⊓ ae volume)
        (𝓝 (profileLeft N c x)) from by
        apply (weighted_profile_left_limit N c x).mono_left
        change (𝓝[≤] x ⊓ ae volume) ≤ (𝓝 x ⊓ 𝓟 (Iio x))
        apply le_inf
        · exact inf_le_left.trans nhdsWithin_le_nhds
        · apply le_principal_iff.mpr
          filter_upwards [show ∀ᶠ y in 𝓝[≤] x ⊓ ae volume, y≤x from
              Filter.Eventually.filter_mono inf_le_left
                (self_mem_nhdsWithin : ∀ᶠ y in 𝓝[≤] x, y≤x),
            show ∀ᶠ y in 𝓝[≤] x ⊓ ae volume, y≠x from
              Filter.Eventually.filter_mono inf_le_right (show ∀ᵐ y ∂volume, y≠x from by
                simpa using (Set.countable_singleton x).ae_notMem volume)]
            with y hy hn
          exact lt_of_le_of_ne hy hn)
  exact h.mono Iio_subset_Iic_self

theorem primitive_regular_derivative (N : ℕ) (c : ℕ → ℝ) (x : ℝ)
    (hx : regularAt N x) :
    HasDerivAt (sourcePrimitive N c) (weightedProfile N c x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (profile_integrable N c 0 x)
    (profile_measurable N c).stronglyMeasurable.stronglyMeasurableAtFilter
    (weighted_profile_derivative c x hx).continuousAt

theorem clock_first_moment {j : ℕ} (hj : 0 < j) :
    (∫ x in (0 : ℝ)..1, x*midpointRow j x)=1/(12*(j : ℝ)) := by
  have he : (∫ x in (0 : ℝ)..1, x*midpointRow j x)=
      ∫ x in (0 : ℝ)..1, midpointRow j x*midpointRow 1 x+(1/2)*midpointRow j x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    have hf : midpointRow 1 x=x-1/2 := by
      simp [midpointRow, affineRow, Int.fract_eq_self.mpr ⟨hx.1.le,hx.2⟩, hx.1.ne']
    rw [hf]
    ring
  rw [he, intervalIntegral.integral_add (midpointProduct_intervalIntegrable hj (by decide) 0 1)
    ((midpointRow_intervalIntegrable hj 0 1).const_mul _),
    midpoint_ramp_gram hj (by decide), intervalIntegral.integral_const_mul, midpointRow_mean_zero hj]
  simp

theorem profile_first_moment (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, x*weightedProfile N c x)=reciprocalMoment N c/6 := by
  have he (x : ℝ) : x*weightedProfile N c x=
      2*∑ j ∈ Finset.Icc 1 N, c j*(x*midpointRow j x) := by
    simp only [weightedProfile, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hint (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x : ℝ => c j*(x*midpointRow j x)) volume 0 1 :=
    ((midpointRow_intervalIntegrable (Finset.mem_Icc.mp hj).1 0 1).continuousOn_mul
      (show ContinuousOn (fun x : ℝ => x) (uIcc 0 1) from continuous_id.continuousOn)).const_mul (c j)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    hint]
  simp_rw [intervalIntegral.integral_const_mul]
  unfold reciprocalMoment
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [clock_first_moment (Finset.mem_Icc.mp hj).1]
  ring

/-- Title: `The actual integrated midpoint source has mean minus its reciprocal moment over six`. -/
theorem primitive_mean (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, sourcePrimitive N c x) = -reciprocalMoment N c/6 := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := sourcePrimitive N c) (u' := profileRight N c)
    (v := fun x : ℝ => x) (v' := fun _ => (1 : ℝ))
    (primitive_continuous N c).continuousOn continuous_id.continuousOn
    (fun x _ => primitive_right_derivative N c x)
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
    (right_profile_integrable N c 0 1) intervalIntegrable_const
  have he : (∫ x in (0 : ℝ)..1, profileRight N c x*x)=
      ∫ x in (0 : ℝ)..1, x*weightedProfile N c x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [right_profile_ae N c] with x hx
    simp only [hx, mul_comm, implies_true]
  simpa only [mul_one, primitive_one, primitive_zero, zero_mul, sub_zero, zero_sub,
    he, profile_first_moment, neg_div] using hparts

end NField.ResetForests.ShiftedEnergy
