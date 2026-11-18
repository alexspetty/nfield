/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhasePrimitive
/-! # The actual finite reset-phase sum and reflection cancellation -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.ShiftedEnergy

open scoped BigOperators Topology
open Set MeasureTheory NField.Alignment
open CommonResetGram CollisionRampEnergy CommonResetWeightedSources
open CollisionDedekindPairing RealSawtoothDistribution FibreTraces

def resetAddresses (d : ℕ) : Finset ℕ :=
  (Finset.Ico 1 d).filter (fun a => a.Coprime d)

def resetPhase (q d a : ℕ) : ℝ := Int.fract ((q : ℝ)*((a : ℝ)/d))

def squaredResetJump (N : ℕ) (c : ℕ → ℝ) (d a : ℕ) : ℝ :=
  -4*resetWeight N c d*weightedProfile N c ((a : ℝ)/d)

def phaseJumpProfile (N q : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
    if resetPhase q d a ≤ ρ then squaredResetJump N c d a else 0

theorem reset_address_bounds {d a : ℕ} (ha : a ∈ resetAddresses d) :
    0<a ∧ a<d ∧ a.Coprime d := by
  obtain ⟨ha,hcop⟩ := Finset.mem_filter.mp ha
  exact ⟨(Finset.mem_Ico.mp ha).1,(Finset.mem_Ico.mp ha).2,hcop⟩

theorem reset_address_reflection {d a : ℕ} (ha : a ∈ resetAddresses d) :
    d-a ∈ resetAddresses d := by
  obtain ⟨ha0,had,hcop⟩ := reset_address_bounds ha
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩, ?_⟩
  exact (Nat.coprime_self_sub_left had.le).mpr hcop

theorem midpoint_sawtooth_odd (x : ℝ) : periodicSawtooth (-x)= -periodicSawtooth x := by
  by_cases hx : Int.fract x=0
  · simp [periodicSawtooth,hx,Int.fract_neg_eq_zero.mpr hx]
  · have hn : Int.fract (-x)≠0 := fun h => hx (Int.fract_neg_eq_zero.mp h)
    rw [periodicSawtooth,if_neg hn,periodicSawtooth,if_neg hx,Int.fract_neg hx]
    ring

theorem profile_reflection (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    weightedProfile N c (1-x)= -weightedProfile N c x := by
  unfold weightedProfile
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : (j : ℝ)*(1-x)= -((j : ℝ)*x)+(j : ℝ) := by ring
  change c j*periodicSawtooth ((j : ℝ)*(1-x))= -(c j*periodicSawtooth ((j : ℝ)*x))
  rw [he, sawtooth_add_nat, midpoint_sawtooth_odd]
  ring

theorem jump_reflection {d a : ℕ} (ha : a ∈ resetAddresses d) (N : ℕ) (c : ℕ → ℝ) :
    squaredResetJump N c d (d-a)= -squaredResetJump N c d a := by
  obtain ⟨_,had,_⟩ := reset_address_bounds ha
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : 0<d).ne'
  have he : (((d-a : ℕ) : ℝ)/d)=1-(a : ℝ)/d := by
    rw [Nat.cast_sub had.le]
    field_simp
  unfold squaredResetJump
  rw [he, profile_reflection]
  ring

theorem denominator_jump_sum_zero (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    (∑ a ∈ resetAddresses d, squaredResetJump N c d a)=0 := by
  have hs : (∑ a ∈ resetAddresses d, squaredResetJump N c d a)=
      ∑ a ∈ resetAddresses d, -squaredResetJump N c d a := by
    apply Finset.sum_bij (fun a _ => d-a)
    · exact fun a ha => reset_address_reflection ha
    · intro a ha b hb he
      have := reset_address_bounds ha
      have := reset_address_bounds hb
      omega
    · intro a ha
      refine ⟨d-a, reset_address_reflection ha, ?_⟩
      have := reset_address_bounds ha
      omega
    · intro a ha
      rw [jump_reflection ha]
      ring
  rw [Finset.sum_neg_distrib] at hs
  linarith

/-- Title: `Reflection cancels the complete nonorigin squared-energy jump mass`. -/
theorem total_jump_sum_zero (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d, squaredResetJump N c d a)=0 := by
  simp only [denominator_jump_sum_zero, Finset.sum_const_zero]

theorem phase_nonnegative (q d a : ℕ) : 0 ≤ resetPhase q d a := Int.fract_nonneg _

theorem phase_less_one (q d a : ℕ) : resetPhase q d a < 1 := Int.fract_lt_one _

theorem phase_positive {q d a : ℕ} (hq : q.Coprime d) (ha : a ∈ resetAddresses d) :
    0 < resetPhase q d a := by
  obtain ⟨ha0,had,hcop⟩ := reset_address_bounds ha
  apply lt_of_le_of_ne (phase_nonnegative q d a)
  intro hz
  have hdiv := (rational_contact_iff (by omega : 0<d) hcop q).mp hz.symm
  have hg : d=1 := by
    have h := hq.gcd_eq_one
    rw [Nat.gcd_eq_right hdiv] at h
    exact h
  omega

theorem step_integrable (t w a b : ℝ) :
    IntervalIntegrable (fun x => if t≤x then w else 0) volume a b := by
  change IntervalIntegrable ((Ici t).indicator (fun _ : ℝ => w)) volume a b
  have hi : IntervalIntegrable (fun _ : ℝ => w) volume a b := intervalIntegrable_const
  exact ⟨hi.1.indicator measurableSet_Ici,hi.2.indicator measurableSet_Ici⟩

theorem step_integral {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (w : ℝ) :
    (∫ x in (0 : ℝ)..1, if t≤x then w else 0)=(1-t)*w := by
  have hleft : (∫ x in (0 : ℝ)..t, if t≤x then w else 0)=0 := by
    calc
      _ = ∫ _x in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht0
        intro x hx
        exact if_neg (not_le_of_gt hx.2)
      _ = 0 := by simp
  have hright : (∫ x in t..1, if t≤x then w else 0)=(1-t)*w := by
    calc
      _ = ∫ _x in t..1, w := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht1
        intro x hx
        exact if_pos hx.1.le
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (step_integrable t w 0 t) (step_integrable t w t 1), hleft, hright, zero_add]

theorem phase_jump_integrable (N q : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (phaseJumpProfile N q c) volume a b := by
  unfold phaseJumpProfile
  exact ⟨integrable_finsetSum _ (fun d _ => integrable_finsetSum _
      (fun a' _ => (step_integrable (resetPhase q d a') (squaredResetJump N c d a') a b).1)),
    integrable_finsetSum _ (fun d _ => integrable_finsetSum _
      (fun a' _ => (step_integrable (resetPhase q d a') (squaredResetJump N c d a') a b).2))⟩

theorem phase_jump_integral_raw (N q : ℕ) (c : ℕ → ℝ) :
    (∫ ρ in (0 : ℝ)..1, phaseJumpProfile N q c ρ)=
      ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        (1-resetPhase q d a)*squaredResetJump N c d a := by
  unfold phaseJumpProfile
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d _
    rw [intervalIntegral.integral_finsetSum (fun a _ => step_integrable _ _ _ _)]
    apply Finset.sum_congr rfl
    intro a _
    exact step_integral (phase_nonnegative q d a) (phase_less_one q d a).le _
  · intro d _
    exact ⟨integrable_finsetSum _ (fun a _ =>
        (step_integrable (resetPhase q d a) (squaredResetJump N c d a) 0 1).1),
      integrable_finsetSum _ (fun a _ =>
        (step_integrable (resetPhase q d a) (squaredResetJump N c d a) 0 1).2)⟩

theorem phase_midpoint_reading {q d a : ℕ} (hq : q.Coprime d) (ha : a ∈ resetAddresses d) :
    midpointRow q ((a : ℝ)/d)=resetPhase q d a-1/2 := by
  exact if_neg (phase_positive hq ha).ne'

/-- Title: `The integral of the literal cumulative phase jump equals the full signed clock query`. -/
theorem phase_jump_integral (N q : ℕ) (c : ℕ → ℝ)
    (hcop : ∀ d ∈ Finset.Icc 2 N, q.Coprime d) :
    (∫ ρ in (0 : ℝ)..1, phaseJumpProfile N q c ρ)=4*weightedInterior N q c := by
  rw [phase_jump_integral_raw]
  unfold weightedInterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hz := denominator_jump_sum_zero N c d
  have he (a : ℕ) (ha : a ∈ resetAddresses d) :
      (1-resetPhase q d a)*squaredResetJump N c d a=
      squaredResetJump N c d a/2+
        4*resetWeight N c d*(weightedProfile N c ((a : ℝ)/d)*midpointRow q ((a : ℝ)/d)) := by
    rw [phase_midpoint_reading (hcop d hd) ha]
    unfold squaredResetJump
    ring
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.sum_div, hz, zero_div, zero_add]
  simp only [resetAddresses, Finset.mul_sum, mul_assoc]

end NField.ResetForests.ShiftedEnergy
