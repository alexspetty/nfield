/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseEnergy
/-! # Actual one-sided energy and cumulative phase-jump readings -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ShiftedEnergy

open scoped BigOperators Topology
open Filter Set MeasureTheory NField.Alignment
open CommonResetGram CommonResetWeightedSources SourceMetrics FibreTraces

def shiftedLeftSum (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ a : Fin Q, profileLeft N c (((a.val : ℝ)+ρ)/(Q : ℝ))^2

def shiftedRightSum (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ a : Fin Q, profileRight N c (((a.val : ℝ)+ρ)/(Q : ℝ))^2

def phaseLeftSum (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
    if resetPhase Q d a < ρ then squaredResetJump N c d a else 0

theorem reduced_contact_weight {d a : ℕ} (hd : 0<d) (ha : a.Coprime d)
    (N : ℕ) (c : ℕ → ℝ) :
    contactMass N c ((a : ℝ)/d)=resetWeight N c d := by
  simp only [contactMass,resetWeight,rational_contact_iff hd ha]

theorem reduced_field_jump {d a : ℕ} (hd : 0<d) (ha : a.Coprime d)
    (N : ℕ) (c : ℕ → ℝ) :
    profileRight N c ((a : ℝ)/d)-profileLeft N c ((a : ℝ)/d)= -2*resetWeight N c d := by
  simp only [profileRight,profileLeft,reduced_contact_weight hd ha]
  ring

theorem reduced_squared_jump {d a : ℕ} (hd : 0<d) (ha : a.Coprime d)
    (N : ℕ) (c : ℕ → ℝ) :
    profileRight N c ((a : ℝ)/d)^2-profileLeft N c ((a : ℝ)/d)^2=
      squaredResetJump N c d a := by
  simp only [profileRight,profileLeft,reduced_contact_weight hd ha,squaredResetJump]
  ring

theorem midpoint_trace_mean (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (profileRight N c x+profileLeft N c x)/2=weightedProfile N c x := by
  unfold profileRight profileLeft
  ring

/-- Title: `The average squared traces differs from the assigned midpoint square by the exact contact square`. -/
theorem midpoint_square_correction (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (profileRight N c x^2+profileLeft N c x^2)/2=
      weightedProfile N c x^2+contactMass N c x^2 := by
  unfold profileRight profileLeft
  ring

theorem shifted_sum_left_limit {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (shiftedEnergySum N Q c) (𝓝[<] ρ) (𝓝 (shiftedLeftSum N Q c ρ)) :=
  tendsto_finsetSum _ (fun a _ =>
    ((weighted_profile_left_limit N c _).comp (affine_fibre_left_limit hQ a.val ρ)).pow 2)

theorem shifted_sum_right_limit {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (shiftedEnergySum N Q c) (𝓝[>] ρ) (𝓝 (shiftedRightSum N Q c ρ)) :=
  tendsto_finsetSum _ (fun a _ =>
    ((weighted_profile_right_limit N c _).comp (affine_fibre_right_limit hQ a.val ρ)).pow 2)

theorem shifted_sum_jump (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    shiftedRightSum N Q c ρ-shiftedLeftSum N Q c ρ=
      ∑ a : Fin Q, -4*contactMass N c (((a.val : ℝ)+ρ)/(Q : ℝ))*
        weightedProfile N c (((a.val : ℝ)+ρ)/(Q : ℝ)) := by
  unfold shiftedRightSum shiftedLeftSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold profileRight profileLeft
  ring

theorem shifted_sum_midpoint_correction (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    (shiftedRightSum N Q c ρ+shiftedLeftSum N Q c ρ)/2=
      shiftedEnergySum N Q c ρ+
        ∑ a : Fin Q, contactMass N c (((a.val : ℝ)+ρ)/(Q : ℝ))^2 := by
  unfold shiftedRightSum shiftedLeftSum shiftedEnergySum
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => midpoint_square_correction N c _)

theorem step_right_limit (t w ρ : ℝ) :
    Tendsto (fun x => if t≤x then w else 0) (𝓝[>] ρ) (𝓝 (if t≤ρ then w else 0)) := by
  by_cases ht : t≤ρ
  · rw [if_pos ht]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (if_pos (le_trans ht (show ρ<x from hx).le)).symm
  · rw [if_neg ht]
    apply tendsto_const_nhds.congr'
    have hm : Iio t ∈ 𝓝[>] ρ := nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ht))
    filter_upwards [hm] with x hx
    exact (if_neg (not_le_of_gt hx)).symm

theorem step_left_limit (t w ρ : ℝ) :
    Tendsto (fun x => if t≤x then w else 0) (𝓝[<] ρ) (𝓝 (if t<ρ then w else 0)) := by
  by_cases ht : t<ρ
  · rw [if_pos ht]
    apply tendsto_const_nhds.congr'
    have hm : Ioi t ∈ 𝓝[<] ρ := nhdsWithin_le_nhds (Ioi_mem_nhds ht)
    filter_upwards [hm] with x hx
    exact (if_pos hx.le).symm
  · rw [if_neg ht]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (if_neg (not_le_of_gt (lt_of_lt_of_le (show x<ρ from hx) (le_of_not_gt ht)))).symm

theorem phase_jump_right_limit (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (phaseJumpProfile N Q c) (𝓝[>] ρ) (𝓝 (phaseJumpProfile N Q c ρ)) :=
  tendsto_finsetSum _ (fun d _ => tendsto_finsetSum _ (fun a _ =>
    step_right_limit (resetPhase Q d a) (squaredResetJump N c d a) ρ))

theorem phase_jump_left_limit (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (phaseJumpProfile N Q c) (𝓝[<] ρ) (𝓝 (phaseLeftSum N Q c ρ)) :=
  tendsto_finsetSum _ (fun d _ => tendsto_finsetSum _ (fun a _ =>
    step_left_limit (resetPhase Q d a) (squaredResetJump N c d a) ρ))

theorem phase_jump_size (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    phaseJumpProfile N Q c ρ-phaseLeftSum N Q c ρ=
      ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        if resetPhase Q d a=ρ then squaredResetJump N c d a else 0 := by
  unfold phaseJumpProfile phaseLeftSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : resetPhase Q d a=ρ
  · simp [he]
  · by_cases hl : resetPhase Q d a<ρ
    · simp [he,hl,hl.le]
    · have hr : ρ<resetPhase Q d a := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      simp [he,hl,not_le_of_gt hr]

theorem phase_jump_zero (N Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d ∈ Finset.Icc 2 N, Q.Coprime d) : phaseJumpProfile N Q c 0=0 := by
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro a ha
  exact if_neg (not_le_of_gt (phase_positive (hc d hd) ha))

theorem phase_jump_one (N Q : ℕ) (c : ℕ → ℝ) : phaseJumpProfile N Q c 1=0 := by
  unfold phaseJumpProfile
  simp only [if_pos (phase_less_one Q _ _).le, denominator_jump_sum_zero, Finset.sum_const_zero]

theorem phase_jump_origin_right_limit (N Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d ∈ Finset.Icc 2 N, Q.Coprime d) :
    Tendsto (phaseJumpProfile N Q c) (𝓝[>] 0) (𝓝 0) := by
  simpa only [phase_jump_zero N Q c hc] using phase_jump_right_limit N Q c 0

theorem step_derivative {t ρ : ℝ} (hne : t≠ρ) (w : ℝ) :
    HasDerivAt (fun x => if t≤x then w else 0) 0 ρ := by
  rcases lt_or_gt_of_ne hne with ht|ht
  · apply (hasDerivAt_const ρ w).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact if_pos hx.le
  · apply (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact if_neg (not_le_of_gt hx)

theorem phase_jump_derivative (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ)
    (hne : ∀ d ∈ Finset.Icc 2 N, ∀ a ∈ resetAddresses d, resetPhase Q d a≠ρ) :
    HasDerivAt (phaseJumpProfile N Q c) 0 ρ := by
  have h := HasDerivAt.fun_sum (u := Finset.Icc 2 N) (fun d hd =>
    HasDerivAt.fun_sum (u := resetAddresses d) (fun a ha =>
      step_derivative (hne d hd a ha) (squaredResetJump N c d a)))
  convert! h using 1
  simp only [Finset.sum_const_zero]

theorem phase_jump_integral_signed (N Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d ∈ Finset.Icc 2 N, Q.Coprime d) :
    (∫ ρ in (0 : ℝ)..1, phaseJumpProfile N Q c ρ)=
      -(∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        squaredResetJump N c d a*CollisionRampEnergy.midpointRow Q ((a : ℝ)/d)) := by
  have he : (∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
      squaredResetJump N c d a*CollisionRampEnergy.midpointRow Q ((a : ℝ)/d))=
      CommonResetWeightedCurvature.valueJumpPhaseSum N Q c := rfl
  rw [phase_jump_integral N Q c hc, he, CommonResetWeightedCurvature.valueJumpPhaseSum_eq]
  ring

theorem prime_square_coprime_inputs {p : ℕ} (hp : p.Prime) :
    (∀ j ∈ Finset.Icc 1 (p-1), j.Coprime (p^2)) ∧
    (∀ d ∈ Finset.Icc 2 (p-1), (p^2).Coprime d) := by
  constructor
  · exact fun _ hj => Core.prime_cutoff_coprime hp hj
  · intro d hd
    exact (Core.prime_cutoff_coprime hp (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hd).1; omega,(Finset.mem_Icc.mp hd).2⟩)).symm

theorem prime_square_jump_integral {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, phaseJumpProfile (p-1) (p^2) c ρ)=
      4*weightedInterior (p-1) (p^2) c :=
  phase_jump_integral _ _ c (prime_square_coprime_inputs hp).2

theorem prime_square_origin_normalization {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    Tendsto (correctedPhaseEnergy (p-1) (p^2) c) (𝓝[>] 0) (𝓝 0) :=
  corrected_phase_origin_right_limit (pow_pos hp.pos 2) (prime_square_coprime_inputs hp).1 c

end NField.ResetForests.ShiftedEnergy
