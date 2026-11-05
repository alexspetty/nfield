/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSieveBound
import NField.Alignment.HarperSmoothingConditioning

/-!
# Finite sieve estimates for the smoothing terms

The rough remainder is bounded by an explicit interval-count term plus
an ordinary harmonic sum. The short-interval weight retains the literal
endpoints and has bound 2/log(P)+(X+1)*P^4/t.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace NField.Alignment.HarperSieveApplications

open HarperSmoothRough HarperIntervalSieve HarperSieveBound HarperRoughSmoothing
  HarperRoundedCutoff HarperSmoothingConditioning

theorem roughAverageSupport_card_le {x P : ℝ} (hx : 0 ≤ x) (hP : 2 ≤ P) (y : ℝ) :
    ((roughAverageSupport ⌊x⌋₊ P y).card : ℝ) ≤ 2*x/Real.log P+P^4 := by
  have hsub : roughAverageSupport ⌊x⌋₊ P y ⊆
      (intervalSupport 0 x).filter (fun n => n.Coprime (primeBase P)) := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hnI, hny, hnP⟩
    refine mem_filter.mpr ⟨?_, hnP⟩
    simpa only [intervalSupport, Nat.floor_zero] using
      (mem_Ioc.mpr (mem_Icc.mp hnI) : n ∈ Ioc 0 ⌊x⌋₊)
  have hc : ((roughAverageSupport ⌊x⌋₊ P y).card : ℝ) ≤
      (((intervalSupport 0 x).filter (fun n => n.Coprime (primeBase P))).card : ℝ) :=
    by exact_mod_cast card_le_card hsub
  exact hc.trans (by simpa using rough_interval_bound (a := 0) (by norm_num) hx hP)

theorem rough_reciprocal_le {x : ℝ} (hx : 1 ≤ x) (P y : ℝ) :
    (∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, (m : ℝ)⁻¹) ≤ 1+Real.log x := by
  calc
    _ ≤ ∑ m ∈ Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (harmonic ⌊x⌋₊ : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ _ := harmonic_floor_le_one_add_log x hx

theorem roughSmoothingError_bound {x P X : ℝ} (hx : 1 ≤ x) (hP : 2 ≤ P)
    (hX : 0 < X) (y : ℝ) :
    roughSmoothingError x P y X ≤ 2*x/Real.log P+P^4+x/X*(1+Real.log x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  calc
    roughSmoothingError x P y X =
        ((roughAverageSupport ⌊x⌋₊ P y).card : ℝ) +
          x/X * ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, (m : ℝ)⁻¹ := by
      unfold roughSmoothingError
      rw [sum_add_distrib, mul_sum]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
      apply sum_congr rfl
      intro m hm
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ _ := add_le_add (roughAverageSupport_card_le hx0 hP y)
      (mul_le_mul_of_nonneg_left (rough_reciprocal_le hx P y) (div_nonneg hx0 hX.le))

def roughShortWeight (t P X : ℝ) : ℝ :=
  ∑ m ∈ (intervalSupport (t/(1+1/X)) t).filter (fun n => n.Coprime (primeBase P)), X/(m : ℝ)

theorem short_lower_identity {t X : ℝ} (hX : 0 < X) :
    t/(1+1/X) = t*X/(X+1) := by
  field_simp

theorem roughShortWeight_bound {t P X : ℝ} (ht : 0 < t) (hP : 2 ≤ P) (hX : 0 < X) :
    roughShortWeight t P X ≤ 2/Real.log P + (X+1)*P^4/t := by
  have hXp : 0 < X+1 := by linarith
  have ha : 0 ≤ t/(1+1/X) := by positivity
  have hat : t/(1+1/X) ≤ t := by
    rw [short_lower_identity hX]
    exact (div_le_iff₀ hXp).mpr (by nlinarith)
  let D := (intervalSupport (t/(1+1/X)) t).filter (fun n => n.Coprime (primeBase P))
  have hm_bound : ∀ m ∈ D, X/(m : ℝ) ≤ (X+1)/t := by
    intro m hm
    have hmI := (intervalSupport_mem ha hat m).mp (mem_filter.mp hm).1
    have hmpos : (0 : ℝ) < m := ha.trans_lt hmI.1
    rw [short_lower_identity hX] at hmI
    apply (div_le_div_iff₀ hmpos ht).mpr
    have h := (div_lt_iff₀ hXp).mp hmI.1
    nlinarith
  calc
    roughShortWeight t P X ≤ ∑ _m ∈ D, (X+1)/t := sum_le_sum hm_bound
    _ = ((D.card : ℝ) * ((X+1)/t)) := by simp
    _ ≤ (2*(t-t/(1+1/X))/Real.log P+P^4)*((X+1)/t) :=
      mul_le_mul_of_nonneg_right (rough_interval_bound ha hat hP) (by positivity)
    _ = 2/Real.log P + (X+1)*P^4/t := by
      rw [short_lower_identity hX]
      field_simp
      ring

theorem roughShortWeight_le_three {t P X : ℝ} (ht : 0 < t) (hP : 2 ≤ P) (hX : 0 < X)
    (hscale : (X+1)*P^4*Real.log P ≤ t) : roughShortWeight t P X ≤ 3/Real.log P := by
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have he : (X+1)*P^4/t ≤ 1/Real.log P := (div_le_div_iff₀ ht hlog).mpr (by simpa using hscale)
  have hb := roughShortWeight_bound ht hP hX
  calc
    _ ≤ 2/Real.log P + 1/Real.log P := hb.trans (add_le_add le_rfl he)
    _ = _ := by ring

end NField.Alignment.HarperSieveApplications
