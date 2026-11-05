/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPositiveRegrouping

/-!
# Exact complete extrema for full-amplitude conductor cutoffs

Universal beta positivity gives the unique simultaneous remainder minimum.
The complementary remainder gap gives the maximum. The cutoff is finite;
the amplitudes in its coefficients are the actual infinite amplitudes.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorExtrema

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionFiniteRegrouping CollisionConductorOne
open CollisionPositiveRegrouping CollisionOdometerRecurrence CollisionCylinderOne

theorem beta_pos {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) : 0 < beta d Q :=
  (div_pos (collisionWeight_pos hd) (by norm_num)).trans (beta_strict_half hd hdQ)

theorem fixedConductor_lower (Q a : ℕ) : -conductorEndpoint Q ≤ fixedConductorValue Q a := by
  have h := fixedConductor_beta_gap Q a
  have hn : 0 ≤ ∑ d ∈ Finset.Icc 2 Q, beta d Q*((a%d : ℕ) : ℝ) := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).le
      (Nat.cast_nonneg _)
  linarith

theorem fixedConductor_upper_gap (Q a : ℕ) :
    conductorEndpoint Q-fixedConductorValue Q a=
      (2/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1-((a%d : ℕ) : ℝ)) := by
  rw [conductorEndpoint_beta,fixedConductor_regrouping]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold centeredRemainder
  ring

theorem complementRemainder_nonneg {d : ℕ} (hd : 0 < d) (a : ℕ) :
    0 ≤ (d : ℝ)-1-((a%d : ℕ) : ℝ) := by
  have h : ((a%d : ℕ) : ℝ)+1 ≤ (d : ℝ) := by exact_mod_cast Nat.mod_lt a hd
  linarith

theorem fixedConductor_upper (Q a : ℕ) : fixedConductorValue Q a ≤ conductorEndpoint Q := by
  have h := fixedConductor_upper_gap Q a
  have hn : 0 ≤ ∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1-((a%d : ℕ) : ℝ)) := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).le
      (complementRemainder_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega) a)
  linarith

theorem fixedConductor_min_divisors (Q a : ℕ) :
    fixedConductorValue Q a=-conductorEndpoint Q ↔ ∀ d ∈ Finset.Icc 2 Q, d ∣ a := by
  have hn : ∀ d ∈ Finset.Icc 2 Q, 0 ≤ beta d Q*((a%d : ℕ) : ℝ) := by
    intro d hd
    exact mul_nonneg (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).le
      (Nat.cast_nonneg _)
  constructor
  · intro he d hd
    have h := fixedConductor_beta_gap Q a
    have hz : (∑ d ∈ Finset.Icc 2 Q, beta d Q*((a%d : ℕ) : ℝ))=0 := by
      rw [he] at h
      linarith
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz d hd
    have hr := (mul_eq_zero.mp ht).resolve_left
      (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).ne'
    exact Nat.dvd_of_mod_eq_zero (by exact_mod_cast hr)
  · intro hd
    have h := fixedConductor_beta_gap Q a
    have hz : (∑ d ∈ Finset.Icc 2 Q, beta d Q*((a%d : ℕ) : ℝ))=0 := by
      apply Finset.sum_eq_zero
      intro d hdm
      simp [Nat.mod_eq_zero_of_dvd (hd d hdm)]
    rw [hz] at h
    linarith

theorem complementRemainder_zero_iff {d : ℕ} (hd : 0 < d) (a : ℕ) :
    (d : ℝ)-1-((a%d : ℕ) : ℝ)=0 ↔ d ∣ a+1 := by
  have h := remainder_step hd a
  constructor
  · intro he
    by_contra hnd
    rw [if_neg hnd] at h
    have hb : (((a+1)%d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt (a+1) hd
    linarith
  · intro hdiv
    rw [if_pos hdiv,Nat.mod_eq_zero_of_dvd hdiv,Nat.cast_zero] at h
    linarith

theorem fixedConductor_max_divisors (Q a : ℕ) :
    fixedConductorValue Q a=conductorEndpoint Q ↔ ∀ d ∈ Finset.Icc 2 Q, d ∣ a+1 := by
  have hn : ∀ d ∈ Finset.Icc 2 Q, 0 ≤ beta d Q*((d : ℝ)-1-((a%d : ℕ) : ℝ)) := by
    intro d hd
    exact mul_nonneg (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).le
      (complementRemainder_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega) a)
  constructor
  · intro he d hd
    have h := fixedConductor_upper_gap Q a
    have hz : (∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1-((a%d : ℕ) : ℝ)))=0 := by
      rw [he] at h
      linarith
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz d hd
    have hr := (mul_eq_zero.mp ht).resolve_left
      (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).ne'
    exact (complementRemainder_zero_iff (by have := (Finset.mem_Icc.mp hd).1; omega) a).mp hr
  · intro hd
    have h := fixedConductor_upper_gap Q a
    have hz : (∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1-((a%d : ℕ) : ℝ)))=0 := by
      apply Finset.sum_eq_zero
      intro d hdm
      rw [(complementRemainder_zero_iff (by have := (Finset.mem_Icc.mp hdm).1; omega) a).mpr
        (hd d hdm),mul_zero]
    rw [hz] at h
    linarith

theorem cutoffPeriod_dvd_iff (Q a : ℕ) :
    cutoffPeriod Q ∣ a ↔ ∀ d ∈ Finset.Icc 2 Q, d ∣ a := by
  rw [cutoffPeriod,Finset.lcm_dvd_iff]
  constructor
  · intro h d hd
    exact h d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
      (Finset.mem_Icc.mp hd).2⟩)
  · intro h d hd
    by_cases hd1 : d=1
    · simp [hd1]
    exact h d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
      (Finset.mem_Icc.mp hd).2⟩)

theorem fixedConductor_min_iff (Q a : ℕ) :
    fixedConductorValue Q a=-conductorEndpoint Q ↔ cutoffPeriod Q ∣ a := by
  rw [fixedConductor_min_divisors,cutoffPeriod_dvd_iff]

theorem fixedConductor_max_iff (Q a : ℕ) :
    fixedConductorValue Q a=conductorEndpoint Q ↔ cutoffPeriod Q ∣ a+1 := by
  rw [fixedConductor_max_divisors,cutoffPeriod_dvd_iff]

theorem fixedConductor_unique_min {Q a : ℕ} (ha : a < cutoffPeriod Q) :
    fixedConductorValue Q a=-conductorEndpoint Q ↔ a=0 := by
  rw [fixedConductor_min_iff,Nat.dvd_iff_mod_eq_zero,Nat.mod_eq_of_lt ha]

theorem fixedConductor_unique_max {Q a : ℕ} (ha : a < cutoffPeriod Q) :
    fixedConductorValue Q a=conductorEndpoint Q ↔ a=cutoffPeriod Q-1 := by
  rw [fixedConductor_max_iff]
  constructor
  · intro h
    have hle := Nat.le_of_dvd (by omega : 0 < a+1) h
    omega
  · intro h
    rw [h,Nat.sub_add_cancel (cutoffPeriod_pos Q)]

theorem fixedConductor_at_last (Q : ℕ) :
    fixedConductorValue Q (cutoffPeriod Q-1)=conductorEndpoint Q := by
  apply (fixedConductor_max_iff Q _).mpr
  rw [Nat.sub_add_cancel (cutoffPeriod_pos Q)]

theorem complete_conductor_extrema (Q : ℕ) :
    (∀ a : ℕ, -conductorEndpoint Q ≤ fixedConductorValue Q a ∧
      fixedConductorValue Q a ≤ conductorEndpoint Q) ∧
    (∀ a : ℕ, a < cutoffPeriod Q →
      (fixedConductorValue Q a=-conductorEndpoint Q ↔ a=0) ∧
      (fixedConductorValue Q a=conductorEndpoint Q ↔ a=cutoffPeriod Q-1)) := by
  exact ⟨fun a => ⟨fixedConductor_lower Q a,fixedConductor_upper Q a⟩,
    fun _ ha => ⟨fixedConductor_unique_min ha,fixedConductor_unique_max ha⟩⟩

end NField.Alignment.CollisionConductorExtrema
