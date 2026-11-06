/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDedekindPairing
import NField.Alignment.ConductorFourFloors

/-! # The first periodic Bernoulli distribution formula for every real argument -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PeriodicBernoulliDistribution

open scoped BigOperators
open NField.Alignment.CollisionDedekindPairing
open NField.Alignment.ConductorFourLifts
open NField.Alignment.ConductorFourFloors

theorem signedSawtooth_eq_periodicSawtooth {q : ℕ} (hq : 0 < q) (k : ℤ) :
    (signedSawtooth k q : ℝ) = periodicSawtooth ((k : ℝ) / q) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := congrArg (fun r : ℚ => (r : ℝ)) (signedSawtooth_linear_floor hq k)
  push_cast at h
  have hf : Int.fract ((k : ℝ) / q) = (k : ℝ) / q - ((k / (q : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract, Int.floor_div_natCast, Int.floor_intCast]
  have hz : Int.fract ((k : ℝ) / q) = 0 ↔ (q : ℤ) ∣ k := by
    rw [Int.fract_div_intCast_eq_div_intCast_mod, div_eq_zero_iff]
    simp only [hqR, or_false, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]
  by_cases hd : (q : ℤ) ∣ k
  · have hf0 := hz.mpr hd
    norm_num [hd] at h
    rw [periodicSawtooth, hf0, if_pos rfl]
    exact_mod_cast h
  · have hfne : Int.fract ((k : ℝ) / q) ≠ 0 := fun hh => hd (hz.mp hh)
    rw [periodicSawtooth, if_neg hfne, hf]
    norm_num [hd] at h
    exact h

theorem periodicSawtooth_periodic : Function.Periodic periodicSawtooth 1 := by
  intro x
  simp [periodicSawtooth, Int.fract_add_one]

theorem periodicSawtooth_fract (x : ℝ) :
    periodicSawtooth (Int.fract x) = periodicSawtooth x := by
  simp [periodicSawtooth, Int.fract_fract]

theorem periodicSawtooth_cell {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    periodicSawtooth x = x - 1 / 2 + if x = 0 then 1 / 2 else 0 := by
  rw [periodicSawtooth, Int.fract_eq_self.mpr ⟨hx0, hx1⟩]
  split_ifs with hx <;> simp_all

def distributionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, periodicSawtooth ((x + j) / n)

theorem distributionSum_periodic {n : ℕ} (hn : 0 < n) :
    Function.Periodic (distributionSum n) 1 := by
  intro x
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := Finset.sum_range_succ' (fun j : ℕ => periodicSawtooth ((x + j) / n)) n
  rw [Finset.sum_range_succ] at h
  have hlast : periodicSawtooth ((x + n) / n) = periodicSawtooth (x / n) := by
    rw [add_div, div_self hnR, periodicSawtooth_periodic]
  have hshift : (∑ j ∈ Finset.range n, periodicSawtooth ((x + (j + 1 : ℕ)) / n)) =
      distributionSum n (x + 1) := by
    unfold distributionSum
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  rw [hlast, hshift] at h
  simp only [Nat.cast_zero, add_zero] at h
  change distributionSum n (x + 1) = distributionSum n x
  change distributionSum n x + periodicSawtooth (x / n) =
    distributionSum n (x + 1) + periodicSawtooth (x / n) at h
  linarith

theorem distributionSum_cell {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    distributionSum n x = periodicSawtooth x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) :
      periodicSawtooth ((x + j) / n) =
      (x + j) / n - 1 / 2 + if x = 0 ∧ j = 0 then 1 / 2 else 0 := by
    have hjn : (j : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hu0 : 0 ≤ (x + j) / n := by positivity
    have hu1 : (x + j) / n < 1 := (div_lt_one hnR).mpr (by linarith)
    rw [periodicSawtooth_cell hu0 hu1]
    have hz : (x + (j : ℝ)) / n = 0 ↔ x = 0 ∧ j = 0 := by
      rw [div_eq_zero_iff]
      simp only [hnR.ne', or_false]
      constructor
      · intro h
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hx : x = 0 := by linarith
        refine ⟨hx, ?_⟩
        have : (j : ℝ) = 0 := by linarith
        exact_mod_cast this
      · rintro ⟨rfl, rfl⟩
        simp
    simp only [hz]
  have hsumj : (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Finset.sum_range_id_mul_two n)
    push_cast at h
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at h
    norm_num at h
    nlinarith
  have herror : (∑ j ∈ Finset.range n, if x = 0 ∧ j = 0 then (1 / 2 : ℝ) else 0) =
      if x = 0 then 1 / 2 else 0 := by
    by_cases hx : x = 0 <;> simp [hx, Finset.mem_range, hn]
  unfold distributionSum
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, herror,
    Finset.sum_sub_distrib]
  simp_rw [add_div]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hsumj]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [periodicSawtooth_cell hx0 hx1]
  field_simp [hnR.ne']
  ring

theorem distributionSum_eq_sawtooth {n : ℕ} (hn : 0 < n) (x : ℝ) :
    distributionSum n x = periodicSawtooth x := by
  have hperiod := (distributionSum_periodic hn).sub_int_mul_eq (x := x) ⌊x⌋
  have hfract : distributionSum n (Int.fract x) = distributionSum n x := by
    simpa only [mul_one, Int.fract] using hperiod
  rw [← hfract, distributionSum_cell hn (Int.fract_nonneg x) (Int.fract_lt_one x),
    periodicSawtooth_fract]

/-- Title: `The periodic Bernoulli distribution formula holds at every real argument`. -/
theorem periodicSawtooth_distribution {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (∑ j ∈ Finset.range n, periodicSawtooth (x + (j : ℝ) / n)) =
      periodicSawtooth ((n : ℝ) * x) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := distributionSum_eq_sawtooth hn ((n : ℝ) * x)
  unfold distributionSum at h
  simpa only [add_div, mul_div_cancel_left₀ x hnR] using h

end NField.Alignment.PeriodicBernoulliDistribution
