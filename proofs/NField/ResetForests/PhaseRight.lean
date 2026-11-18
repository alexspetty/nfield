/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseTraces
/-! # Right-continuous source readings and their actual derivatives -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PhaseIdentity

open scoped BigOperators Topology
open Filter Set NField.Alignment
open CommonResetGram CollisionRampEnergy CollisionDedekindPairing RealSawtoothLimits
open RealBernoulliBoundaryLimits SourceMetrics FibreReconstruction FibreTraces ShiftedEnergy

theorem right_profile_formula (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    profileRight N c x=2*∑ j ∈ Finset.Icc 1 N, c j*(Int.fract ((j : ℝ)*x)-1/2) := by
  unfold profileRight weightedProfile contactMass
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [midpoint_row_periodic_saw,periodicSawtooth]
  split_ifs with h
  · rw [h]
    ring
  · ring

theorem fract_right_derivative (x : ℝ) :
    HasDerivWithinAt Int.fract 1 (Ici x) x := by
  have he : (Int.floor : ℝ → ℤ) =ᶠ[𝓝[≥] x] fun _ => Int.floor x :=
    tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  apply ((hasDerivAt_id x).sub_const (Int.floor x : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [he] with y hy
    simp only [Int.fract,hy,id_eq]
  · rfl

theorem right_profile_derivative (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (profileRight N c) (2*sourceSlope N c) (Ici x) x := by
  have hj (j : ℕ) :
      HasDerivWithinAt (fun y : ℝ => c j*(Int.fract ((j : ℝ)*y)-1/2))
        (c j*(j : ℝ)) (Ici x) x := by
    have h := (fract_right_derivative ((j : ℝ)*x)).comp x
      ((hasDerivAt_id x).const_mul (j : ℝ)).hasDerivWithinAt
      (by
        intro y hy
        change (j : ℝ)*x≤(j : ℝ)*y
        exact mul_le_mul_of_nonneg_left (show x≤y from hy) (Nat.cast_nonneg j))
    convert! (h.sub_const (1/2 : ℝ)).const_mul (c j) using 1
    ring
  have hs := (HasDerivWithinAt.fun_sum (u := Finset.Icc 1 N) (fun j _ => hj j)).const_mul 2
  convert! hs using 1
  exact funext (right_profile_formula N c)

theorem right_profile_eq_eventually_left (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    profileRight N c =ᶠ[𝓝[<] x] weightedProfile N c := by
  have h := (eventually_all_finset (Finset.Icc 1 N)).mpr
    (fun j hj => Filter.Tendsto.eventually
      (positive_mul_left_limit (by exact_mod_cast (Finset.mem_Icc.mp hj).1) x)
      (eventually_fract_ne_left ((j : ℝ)*x)))
  filter_upwards [h] with y hy
  have hz : contactMass N c y=0 := Finset.sum_eq_zero (fun j hj => if_neg (hy j hj))
  simp only [profileRight,hz,sub_zero]

theorem right_profile_eq_eventually_right (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    profileRight N c =ᶠ[𝓝[>] x] weightedProfile N c := by
  have h := (eventually_all_finset (Finset.Icc 1 N)).mpr
    (fun j hj => Filter.Tendsto.eventually
      (positive_mul_right_limit (by exact_mod_cast (Finset.mem_Icc.mp hj).1) x)
      (eventually_fract_ne_right ((j : ℝ)*x)))
  filter_upwards [h] with y hy
  have hz : contactMass N c y=0 := Finset.sum_eq_zero (fun j hj => if_neg (hy j hj))
  simp only [profileRight,hz,sub_zero]

theorem right_profile_left_limit (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    Tendsto (profileRight N c) (𝓝[<] x) (𝓝 (profileLeft N c x)) :=
  (weighted_profile_left_limit N c x).congr' (right_profile_eq_eventually_left N c x).symm

theorem right_profile_right_limit (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    Tendsto (profileRight N c) (𝓝[>] x) (𝓝 (profileRight N c x)) :=
  (weighted_profile_right_limit N c x).congr' (right_profile_eq_eventually_right N c x).symm

theorem right_coprime_distribution {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ) :
    (∑ a : Fin Q, profileRight N c (((a.val : ℝ)+ρ)/(Q : ℝ)))=profileRight N c ρ := by
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin Q)) (fun a _ =>
    (weighted_profile_right_limit N c _).comp (affine_fibre_right_limit hQ a.val ρ))
  have he : (fun x => ∑ a : Fin Q, weightedProfile N c (((a.val : ℝ)+x)/(Q : ℝ)))=
      weightedProfile N c := funext (weighted_coprime_distribution hQ hc c)
  dsimp only [Function.comp_def] at hs
  rw [he] at hs
  exact tendsto_nhds_unique hs (weighted_profile_right_limit N c ρ)

theorem contact_coprime_distribution {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ) :
    (∑ a : Fin Q, contactMass N c (((a.val : ℝ)+ρ)/(Q : ℝ)))=contactMass N c ρ := by
  have hr := right_coprime_distribution hQ hc c ρ
  simp only [profileRight,Finset.sum_sub_distrib,weighted_coprime_distribution hQ hc c ρ] at hr
  linarith

theorem shifted_right_left_limit {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (shiftedRightSum N Q c) (𝓝[<] ρ) (𝓝 (shiftedLeftSum N Q c ρ)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ =>
    ((right_profile_left_limit N c _).comp (affine_fibre_left_limit hQ a.val ρ)).pow 2)

theorem shifted_right_right_limit {Q : ℕ} (hQ : 0<Q) (N : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    Tendsto (shiftedRightSum N Q c) (𝓝[>] ρ) (𝓝 (shiftedRightSum N Q c ρ)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ =>
    ((right_profile_right_limit N c _).comp (affine_fibre_right_limit hQ a.val ρ)).pow 2)

theorem shifted_right_derivative {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) (c : ℕ → ℝ) (ρ : ℝ) :
    HasDerivWithinAt (shiftedRightSum N Q c)
      ((4*sourceSlope N c/(Q : ℝ))*profileRight N c ρ) (Ici ρ) ρ := by
  have ht (a : Fin Q) :
      HasDerivWithinAt (fun x => profileRight N c (((a.val : ℝ)+x)/(Q : ℝ))^2)
        ((4*sourceSlope N c/(Q : ℝ))*profileRight N c (((a.val : ℝ)+ρ)/(Q : ℝ)))
        (Ici ρ) ρ := by
    have hi : HasDerivAt (fun x : ℝ => ((a.val : ℝ)+x)/(Q : ℝ)) (1/(Q : ℝ)) ρ := by
      simpa only [id_eq] using ((hasDerivAt_id ρ).const_add (a.val : ℝ)).div_const (Q : ℝ)
    have hm : MapsTo (fun x : ℝ => ((a.val : ℝ)+x)/(Q : ℝ)) (Ici ρ)
        (Ici (((a.val : ℝ)+ρ)/(Q : ℝ))) := by
      intro x hx
      change ((a.val : ℝ)+ρ)/(Q : ℝ)≤((a.val : ℝ)+x)/(Q : ℝ)
      apply div_le_div_of_nonneg_right _ (show (0 : ℝ)≤Q from Nat.cast_nonneg _)
      linarith [show ρ≤x from hx]
    convert! ((right_profile_derivative N c _).comp ρ hi.hasDerivWithinAt hm).pow 2 using 1
    norm_num [Function.comp_def]
    ring
  have hs := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ => ht a)
  rw [← Finset.mul_sum,right_coprime_distribution hQ hc c ρ] at hs
  exact hs

theorem step_right_derivative (t w ρ : ℝ) :
    HasDerivWithinAt (fun x : ℝ => if t≤x then w else 0) 0 (Ici ρ) ρ := by
  by_cases ht : t≤ρ
  · apply (hasDerivWithinAt_const ρ (Ici ρ) w).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [if_pos (ht.trans hx)]
    · simp only [if_pos ht]
  · apply (hasDerivWithinAt_const ρ (Ici ρ) (0 : ℝ)).congr_of_eventuallyEq
    · have he : Iio t ∈ 𝓝[≥] ρ := nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ht))
      filter_upwards [he] with x hx
      simp only [if_neg (not_le.mpr (show x<t from hx))]
    · simp only [if_neg ht]

theorem phase_jump_right_derivative (N Q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) :
    HasDerivWithinAt (phaseJumpProfile N Q c) 0 (Ici ρ) ρ := by
  have hs := HasDerivWithinAt.fun_sum (u := Finset.Icc 2 N) (fun d _ =>
    HasDerivWithinAt.fun_sum (u := resetAddresses d) (fun a _ =>
      step_right_derivative (resetPhase Q d a) (squaredResetJump N c d a) ρ))
  convert! hs using 1
  simp only [Finset.sum_const_zero]

end NField.ResetForests.PhaseIdentity
