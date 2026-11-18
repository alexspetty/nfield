/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseJumps
import NField.Alignment.CommonResetWeightedJumps
/-! # The complete shifted sampling grid, with its actual origin reading -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ShiftedEnergy

open scoped BigOperators Topology
open Filter Set MeasureTheory NField.Alignment
open CommonResetGram CollisionRampEnergy CommonResetWeightedDistribution
open SourceMetrics FibreReconstruction FibreTraces

def shiftedEnergySum (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ a : Fin Q, weightedProfile N c (((a.val : ℝ)+ρ)/(Q : ℝ))^2

def shiftedEnergy (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  shiftedEnergySum N Q c ρ/(Q : ℝ)

def correctedPhaseEnergy (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  shiftedEnergySum N Q c ρ-shiftedEnergySum N Q c 0-(sourceTotal N c)^2-
    (4*sourceSlope N c/(Q : ℝ))*sourcePrimitive N c ρ

theorem weighted_coprime_distribution {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ) :
    (∑ a : Fin Q, weightedProfile N c (((a.val : ℝ)+ρ)/(Q : ℝ)))=
      weightedProfile N c ρ := by
  rw [Fin.sum_univ_eq_sum_range
    (fun a : ℕ => weightedProfile N c (((a : ℝ)+ρ)/(Q : ℝ))) Q]
  unfold weightedProfile
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, coprime_midpoint_distribution hQ (hc j hj)]

theorem shifted_energy_sum_integrable {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) :
    IntervalIntegrable (shiftedEnergySum N Q c) volume 0 1 :=
  affine_fibre_sum_integrable hQ _ (weighted_square_integrable N c)

/-- Title: `Averaging every shifted sample label gives exactly the continuous source energy`. -/
theorem shifted_energy_mean {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, shiftedEnergy N Q c ρ)=
      ∫ x in (0 : ℝ)..1, weightedProfile N c x^2 := by
  unfold shiftedEnergy shiftedEnergySum
  rw [intervalIntegral.integral_div,
    affine_fibre_sum_integral hQ _ (weighted_square_integrable N c)]
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  field_simp

theorem shifted_energy_zero (N Q : ℕ) (c : ℕ → ℝ) :
    shiftedEnergy N Q c 0=CommonResetWeightedSampling.weightedSample N Q c := by
  unfold shiftedEnergy shiftedEnergySum CommonResetWeightedSampling.weightedSample
  simp only [add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => weightedProfile N c ((a : ℝ)/(Q : ℝ))^2) Q]
  ring

theorem shifted_energy_sum_derivative {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ)
    (hρ : regularAt N ρ) :
    HasDerivAt (shiftedEnergySum N Q c)
      ((4*sourceSlope N c/(Q : ℝ))*weightedProfile N c ρ) ρ := by
  have ht (a : Fin Q) :
      HasDerivAt (fun x => weightedProfile N c (((a.val : ℝ)+x)/(Q : ℝ))^2)
        ((4*sourceSlope N c/(Q : ℝ))*weightedProfile N c (((a.val : ℝ)+ρ)/(Q : ℝ))) ρ := by
    have hi : HasDerivAt (fun x : ℝ => ((a.val : ℝ)+x)/(Q : ℝ)) (1/(Q : ℝ)) ρ := by
      simpa only [id_eq] using ((hasDerivAt_id ρ).const_add (a.val : ℝ)).div_const (Q : ℝ)
    convert! ((weighted_profile_derivative c _ (regular_at_fibre hQ ρ a.val hρ)).comp ρ hi).pow 2 using 1
    norm_num [Function.comp_def]
    ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => ht a)
  rw [← Finset.mul_sum, weighted_coprime_distribution hQ hc c ρ] at hs
  exact hs

theorem corrected_phase_derivative_zero {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ)
    (hρ : regularAt N ρ) : HasDerivAt (correctedPhaseEnergy N Q c) 0 ρ := by
  have h := (((shifted_energy_sum_derivative hQ hc c ρ hρ).sub_const
    (shiftedEnergySum N Q c 0)).sub_const ((sourceTotal N c)^2)).sub
      ((primitive_regular_derivative N c ρ hρ).const_mul (4*sourceSlope N c/(Q : ℝ)))
  convert! h using 1
  ring

theorem corrected_phase_constant_on_interval {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (a b : ℝ)
    (hregular : ∀ ρ ∈ Ioo a b, regularAt N ρ) {x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    correctedPhaseEnergy N Q c x=correctedPhaseEnergy N Q c y := by
  have hbnd := (convex_Ioo a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun ρ hρ => (corrected_phase_derivative_zero hQ hc c ρ (hregular ρ hρ)).hasDerivWithinAt)
    (by simp) hx hy
  have hz : correctedPhaseEnergy N Q c y-correctedPhaseEnergy N Q c x=0 := by
    apply norm_eq_zero.mp
    exact (show ‖correctedPhaseEnergy N Q c y-correctedPhaseEnergy N Q c x‖ ≤ 0 by
      simpa using hbnd).antisymm (norm_nonneg _)
  exact (sub_eq_zero.mp hz).symm

theorem grid_contact_mass {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (a : Fin Q) :
    contactMass N c ((a.val : ℝ)/(Q : ℝ))=if a.val=0 then sourceTotal N c else 0 := by
  unfold contactMass sourceTotal
  by_cases ha : a.val=0
  · simp [ha]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro j hj
    apply if_neg
    intro hz
    have he : (j : ℝ)*((a.val : ℝ)/(Q : ℝ))=((j*a.val : ℕ) : ℝ)/(Q : ℝ) := by
      push_cast
      ring
    rw [he] at hz
    have hd : Q ∣ j*a.val := (fract_nat_ratio_zero_iff (j*a.val) hQ).mp hz
    have hda : Q ∣ a.val := (hc j hj).symm.dvd_of_dvd_mul_left hd
    exact (Nat.not_dvd_of_pos_of_lt (by omega) a.isLt) hda

theorem right_energy_origin {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    (∑ a : Fin Q, profileRight N c ((a.val : ℝ)/(Q : ℝ))^2)=
      shiftedEnergySum N Q c 0+(sourceTotal N c)^2 := by
  have hp (a : Fin Q) : profileRight N c ((a.val : ℝ)/(Q : ℝ))^2=
      weightedProfile N c ((a.val : ℝ)/(Q : ℝ))^2+
        if a.val=0 then (sourceTotal N c)^2 else 0 := by
    rw [profileRight, grid_contact_mass hQ hc]
    by_cases ha : a.val=0
    · simp [ha, weightedProfile_zero]
    · simp [ha]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  have hz : (∑ a : Fin Q, if a.val=0 then (sourceTotal N c)^2 else 0)=(sourceTotal N c)^2 := by
    let z : Fin Q := ⟨0,hQ⟩
    have he (a : Fin Q) : (a.val=0) ↔ a=z := by
      constructor
      · intro h; exact Fin.ext h
      · rintro rfl; rfl
    simp_rw [he]
    simp
  rw [hz]
  simp only [shiftedEnergySum, add_zero]

/-- Title: `The actual origin midpoint contributes exactly the missing square of the total source`. -/
theorem shifted_energy_origin_right_limit {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    Tendsto (shiftedEnergySum N Q c) (𝓝[>] 0)
      (𝓝 (shiftedEnergySum N Q c 0+(sourceTotal N c)^2)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin Q)) (fun a _ =>
    ((weighted_profile_right_limit N c _).comp (affine_fibre_right_limit hQ a.val 0)).pow 2)
  simp only [add_zero] at h
  rw [right_energy_origin hQ hc] at h
  exact h

theorem corrected_phase_origin_right_limit {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) :
    Tendsto (correctedPhaseEnergy N Q c) (𝓝[>] 0) (𝓝 0) := by
  have hp := (primitive_continuous N c).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  rw [primitive_zero] at hp
  have h := (((shifted_energy_origin_right_limit hQ hc c).sub_const
    (shiftedEnergySum N Q c 0)).sub_const ((sourceTotal N c)^2)).sub
      (hp.const_mul (4*sourceSlope N c/(Q : ℝ)))
  convert! h using 1
  congr 1
  ring

end NField.ResetForests.ShiftedEnergy
