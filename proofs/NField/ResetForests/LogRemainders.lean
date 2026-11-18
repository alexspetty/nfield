/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SourceEnergy
import NField.ResetForests.LoadTail
/-! # The printed logarithmic curvature and normalized load-tail allowances -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RefinedBounds

open scoped BigOperators Topology
open Filter
open NField.Alignment DedekindFourierMoment
open CostCriteria

def harmonicLogConstant : ℝ := 1 + 1 / Real.log 2

theorem harmonic_log_constant_positive : 0 < harmonicLogConstant := by
  have h : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold harmonicLogConstant
  positivity

theorem complete_harmonic_log_bound {p : ℕ} (hp : 2 ≤ p) :
    (harmonic (p - 1) : ℝ) ≤ harmonicLogConstant * Real.log (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hpR
  have h1 : 1 ≤ Real.log (p : ℝ) / Real.log 2 := (one_le_div htwo).mpr hlog
  have hh := (harmonic_cast_mono (Nat.sub_le p 1)).trans (harmonic_le_one_add_log p)
  have he : harmonicLogConstant * Real.log (p : ℝ) =
      Real.log (p : ℝ) + Real.log (p : ℝ) / Real.log 2 := by
    unfold harmonicLogConstant
    ring
  rw [he]
  linarith

def curvature (p : ℕ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) / (3 * (p : ℝ) ^ 3)

theorem cutoff_harmonic_nonnegative (p : ℕ) : 0 ≤ (harmonic (p - 1) : ℝ) := by
  simpa using harmonic_cast_mono (Nat.zero_le (p - 1))

theorem curvature_nonnegative (p : ℕ) : 0 ≤ curvature p := by
  have hh := cutoff_harmonic_nonnegative p
  unfold curvature
  positivity

theorem curvature_log_bound {p : ℕ} (hp : 2 ≤ p) :
    |curvature p| ≤ (harmonicLogConstant / 3) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hN : ((p - 1 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.sub_le p 1)
  rw [abs_of_nonneg (curvature_nonnegative p)]
  unfold curvature
  calc
    _ ≤ (p : ℝ) * (harmonicLogConstant * Real.log (p : ℝ)) / (3 * (p : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hN (complete_harmonic_log_bound hp) (cutoff_harmonic_nonnegative p) hpR.le) (by positivity)
    _ = _ := by field_simp

theorem curvature_log_isBigO :
    Asymptotics.IsBigO primeAtTop (fun p : OddPrime => curvature p.val)
      (fun p : OddPrime => Real.log (p.val : ℝ) / (p.val : ℝ) ^ 2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨harmonicLogConstant / 3, Eventually.of_forall ?_⟩
  intro p
  have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast p.property.1.one_le
  have hl : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg hp1
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  exact curvature_log_bound p.property.1.two_le

theorem normalized_load_tail_log_bound {p : ℕ} {M : ℝ}
    (hp : p.Prime) (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 2 ≤ k ∧ k ≤ p - 1)
    (hload : ∀ k ∈ S, M ≤ (((p - 1) / k : ℕ) : ℝ)) :
    (∑ k ∈ S, |4 * Core.clockReading (p - 1) (p ^ 2) k|) / (p : ℝ) ^ 2 ≤
      (4 * harmonicLogConstant ^ 2) * (Real.log (p : ℝ)) ^ 2 / M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p - 1 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.sub_le p 1)
  have hH : 0 ≤ (harmonic (p - 1) : ℝ) := cutoff_harmonic_nonnegative p
  have hN2 : ((p - 1 : ℕ) : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
  have hH2 : (harmonic (p - 1) : ℝ) ^ 2 ≤
      (harmonicLogConstant * Real.log (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hH (complete_harmonic_log_bound hp.two_le) 2
  have ht := PhasePopulations.reset_load_tail_real hp hM S hS hload
  calc
    _ ≤ (4 * ((p - 1 : ℕ) : ℝ) ^ 2 * (harmonic (p - 1) : ℝ) ^ 2 / M) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (ht.1.trans ht.2) (sq_nonneg _)
    _ ≤ (4 * (p : ℝ) ^ 2 * (harmonicLogConstant * Real.log (p : ℝ)) ^ 2 / M) / (p : ℝ) ^ 2 := by
      gcongr
    _ = _ := by field_simp

end NField.ResetForests.RefinedBounds
