/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseRegularity
/-! # The shifted-grid identity assembled across every reset phase -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PhaseIdentity

open scoped BigOperators Topology
open Filter Set NField.Alignment
open CommonResetGram SourceMetrics FibreReconstruction FibreTraces ShiftedEnergy

def rightPhaseRemainder (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  shiftedRightSum N Q c ρ-shiftedEnergySum N Q c 0-(sourceTotal N c)^2-
    (4*sourceSlope N c/(Q : ℝ))*sourcePrimitive N c ρ-phaseJumpProfile N Q c ρ

theorem right_phase_remainder_derivative {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ) :
    HasDerivWithinAt (rightPhaseRemainder N Q c) 0 (Ici ρ) ρ := by
  have h := ((((shifted_right_derivative hQ hc c ρ).sub_const
    (shiftedEnergySum N Q c 0)).sub_const ((sourceTotal N c)^2)).sub
    (((primitive_right_derivative N c ρ).Ici_of_Ioi).const_mul (4*sourceSlope N c/(Q : ℝ)))).sub
    (phase_jump_right_derivative N Q c ρ)
  convert! h using 1
  ring

theorem right_phase_remainder_right_limit {Q : ℕ} (hQ : 0<Q)
    (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (rightPhaseRemainder N Q c) (𝓝[>] ρ) (𝓝 (rightPhaseRemainder N Q c ρ)) := by
  have hp := (primitive_continuous N c).continuousAt.tendsto.mono_left
    (show 𝓝[>] ρ≤𝓝 ρ from nhdsWithin_le_nhds)
  exact ((((shifted_right_right_limit hQ N c ρ).sub_const
    (shiftedEnergySum N Q c 0)).sub_const ((sourceTotal N c)^2)).sub
    (hp.const_mul (4*sourceSlope N c/(Q : ℝ)))).sub (phase_jump_right_limit N Q c ρ)

theorem right_phase_remainder_left_limit {Q : ℕ} (hQ : 0<Q)
    (N : ℕ) (c : ℕ → ℝ) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 1) :
    Tendsto (rightPhaseRemainder N Q c) (𝓝[<] ρ) (𝓝 (rightPhaseRemainder N Q c ρ)) := by
  have hp := (primitive_continuous N c).continuousAt.tendsto.mono_left
    (show 𝓝[<] ρ≤𝓝 ρ from nhdsWithin_le_nhds)
  have h := ((((shifted_right_left_limit hQ N c ρ).sub_const
    (shiftedEnergySum N Q c 0)).sub_const ((sourceTotal N c)^2)).sub
    (hp.const_mul (4*sourceSlope N c/(Q : ℝ)))).sub (phase_jump_left_limit N Q c ρ)
  have he : shiftedLeftSum N Q c ρ-shiftedEnergySum N Q c 0-(sourceTotal N c)^2-
      (4*sourceSlope N c/(Q : ℝ))*sourcePrimitive N c ρ-phaseLeftSum N Q c ρ=
        rightPhaseRemainder N Q c ρ := by
    unfold rightPhaseRemainder
    have hj := shifted_jump_matches_phase hQ hρ N c
    linarith
  rw [he] at h
  exact h

theorem right_phase_remainder_continuous {Q : ℕ} (hQ : 0<Q)
    (N : ℕ) (c : ℕ → ℝ) {b : ℝ} (hb : b<1) :
    ContinuousOn (rightPhaseRemainder N Q c) (Icc 0 b) := by
  intro x hx
  by_cases hx0 : x=0
  · subst x
    exact (continuousWithinAt_Ioi_iff_Ici.mp
      (right_phase_remainder_right_limit hQ N c 0)).mono (fun y hy => hy.1)
  · have hxI : x ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_lt hx.2 hb⟩
    exact (continuousAt_iff_continuous_left'_right'.mpr
      ⟨right_phase_remainder_left_limit hQ N c hxI,
       right_phase_remainder_right_limit hQ N c x⟩).continuousWithinAt

theorem coprime_reset_denominators {N Q : ℕ}
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) :
    ∀ d ∈ Finset.Icc 2 N, Q.Coprime d := by
  intro d hd
  have hdB := Finset.mem_Icc.mp hd
  exact (hc d (Finset.mem_Icc.mpr ⟨by omega,hdB.2⟩)).symm

theorem right_phase_remainder_zero {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    rightPhaseRemainder N Q c 0=0 := by
  have hr : shiftedRightSum N Q c 0=shiftedEnergySum N Q c 0+(sourceTotal N c)^2 := by
    simpa only [shiftedRightSum,add_zero] using right_energy_origin hQ hc c
  rw [rightPhaseRemainder,hr,primitive_zero,
    phase_jump_zero N Q c (coprime_reset_denominators hc)]
  ring

/-- Title: `Matched jumps, actual right derivatives, and the origin value fix the whole phase reading`. -/
theorem right_phase_remainder_vanishes {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Ico 0 1) : rightPhaseRemainder N Q c ρ=0 := by
  have h := constant_of_has_deriv_right_zero
    (right_phase_remainder_continuous hQ N c hρ.2)
    (fun x _ => right_phase_remainder_derivative hQ hc c x)
    ρ (show ρ ∈ Icc 0 ρ from ⟨hρ.1,le_rfl⟩)
  exact h.trans (right_phase_remainder_zero hQ hc c)

theorem phase_identity_at_regular {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Ico 0 1) (hreg : regularAt N ρ) :
    phaseJumpProfile N Q c ρ=correctedPhaseEnergy N Q c ρ := by
  have h := right_phase_remainder_vanishes hQ hc c hρ
  unfold rightPhaseRemainder at h
  rw [shifted_right_eq_midpoint hQ hreg c] at h
  unfold correctedPhaseEnergy
  linarith

theorem scaled_shifted_energy {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    (Q : ℝ)*shiftedEnergy N Q c ρ=shiftedEnergySum N Q c ρ := by
  unfold shiftedEnergy
  have hQR : (Q : ℝ)≠0 := by exact_mod_cast hQ.ne'
  field_simp

/-- Title: `The printed shifted-grid identity holds off every nonorigin reset phase`. -/
theorem shifted_grid_phase_identity {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 1)
    (hphase : ∀ d ∈ Finset.Icc 2 N, ∀ a ∈ resetAddresses d, resetPhase Q d a≠ρ) :
    phaseJumpProfile N Q c ρ=(Q : ℝ)*shiftedEnergy N Q c ρ-
      (Q : ℝ)*shiftedEnergy N Q c 0-(sourceTotal N c)^2-
      (4*sourceSlope N c/(Q : ℝ))*sourcePrimitive N c ρ := by
  rw [scaled_shifted_energy hQ,scaled_shifted_energy hQ]
  exact phase_identity_at_regular hQ hc c ⟨hρ.1.le,hρ.2⟩
    ((phase_exclusion_iff_regular hQ hc hρ).mp hphase)

theorem prime_square_phase_identity {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 1)
    (hphase : ∀ d ∈ Finset.Icc 2 (p-1), ∀ a ∈ resetAddresses d, resetPhase (p^2) d a≠ρ) :
    phaseJumpProfile (p-1) (p^2) c ρ=(p^2 : ℕ)*shiftedEnergy (p-1) (p^2) c ρ-
      (p^2 : ℕ)*shiftedEnergy (p-1) (p^2) c 0-(sourceTotal (p-1) c)^2-
      (4*sourceSlope (p-1) c/(p^2 : ℕ))*sourcePrimitive (p-1) c ρ :=
  shifted_grid_phase_identity (pow_pos hp.pos _) (prime_square_coprime_inputs hp).1 c hρ hphase

end NField.ResetForests.PhaseIdentity
