/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseIdentity
/-! # Integrating the actual phase identity gives the complete reset formula -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PhaseIdentity

open scoped BigOperators Topology
open Filter Set MeasureTheory NField.Alignment
open CommonResetGram CommonResetWeightedSources CommonResetWeightedSampling
open CommonResetWeightedDistribution SourceMetrics FibreReconstruction FibreTraces ShiftedEnergy

theorem phase_identity_integral {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, phaseJumpProfile N Q c ρ)=
      ∫ ρ in (0 : ℝ)..1, correctedPhaseEnergy N Q c ρ := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [regular_ae N,volume.ae_ne (1 : ℝ)] with ρ hreg hne hρ
  have hb : ρ ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hρ
  exact phase_identity_at_regular hQ hc c ⟨hb.1.le,lt_of_le_of_ne hb.2 hne⟩ hreg

theorem shifted_sum_mean {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, shiftedEnergySum N Q c ρ)=
      (Q : ℝ)*∫ x in (0 : ℝ)..1, weightedProfile N c x^2 :=
  affine_fibre_sum_integral hQ _ (weighted_square_integrable N c)

theorem corrected_phase_integral {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, correctedPhaseEnergy N Q c ρ)=
      (Q : ℝ)*(∫ x in (0 : ℝ)..1, weightedProfile N c x^2)-
      shiftedEnergySum N Q c 0-(sourceTotal N c)^2+
      (2*sourceSlope N c*reciprocalMoment N c)/(3*(Q : ℝ)) := by
  have he := shifted_energy_sum_integrable hQ N c
  have h1 := he.sub (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => shiftedEnergySum N Q c 0) volume 0 1)
  have h2 := h1.sub (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => (sourceTotal N c)^2) volume 0 1)
  have hp : IntervalIntegrable
      (fun ρ => (4*sourceSlope N c/(Q : ℝ))*sourcePrimitive N c ρ) volume 0 1 :=
    ((primitive_continuous N c).intervalIntegrable 0 1).const_mul (4*sourceSlope N c/(Q : ℝ))
  unfold correctedPhaseEnergy
  rw [intervalIntegral.integral_sub h2 hp,intervalIntegral.integral_sub h1 intervalIntegrable_const,
    intervalIntegral.integral_sub he intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul,primitive_mean,shifted_sum_mean hQ]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  ring

/-- Title: `The complete weighted reset identity follows by integrating the phase derivation`. -/
theorem phase_derived_source_identity {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    weightedDefect N Q c=((sourceTotal N c)^2+4*weightedInterior N Q c-
      (2*sourceSlope N c*reciprocalMoment N c)/(3*(Q : ℝ)))/(Q : ℝ) := by
  have h := phase_identity_integral hQ hc c
  rw [phase_jump_integral N Q c (coprime_reset_denominators hc),corrected_phase_integral hQ,
    ← scaled_shifted_energy hQ N c 0,shifted_energy_zero] at h
  have hQR : (Q : ℝ)≠0 := by exact_mod_cast hQ.ne'
  unfold weightedDefect
  apply (eq_div_iff hQR).mpr
  nlinarith

theorem prime_square_phase_derived_source_identity {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    weightedDefect (p-1) (p^2) c=((sourceTotal (p-1) c)^2+4*weightedInterior (p-1) (p^2) c-
      (2*sourceSlope (p-1) c*reciprocalMoment (p-1) c)/(3*(p^2 : ℕ)))/(p^2 : ℕ) :=
  phase_derived_source_identity (pow_pos hp.pos _) (prime_square_coprime_inputs hp).1 c

end NField.ResetForests.PhaseIdentity
