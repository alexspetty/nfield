/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandWeighted
import Mathlib.Data.Nat.Sqrt

/-! # All interval restrictions in the actual conductor bands -/

noncomputable section

namespace NField.Alignment.CommonResetRetainedBands

open scoped BigOperators
open Set CommonResetBandWeighted CommonResetBandPhases CommonResetBandGeometry
open CommonResetBandParameters CommonResetDerivativeIntervals

def originalFrequency (p t u v j : ℕ) : ℝ :=
  gatedPhase p t u v 0 j+gatedPhase p t u v 1 j+gatedPhase p t u v (-1) j

theorem original_frequency_interval (p u v j a N : ℕ) :
    (∑ i ∈ Finset.range (N+1), originalFrequency p (a+i) u v j) =
      frequencyBandSum p u v j a N := by
  simp only [originalFrequency, frequencyBandSum, linkedBandSum, Finset.sum_add_distrib]

theorem quotient_band_membership {p t m : ℕ} (ht : 0 < t) (hm : 0 < m)
    (he : (p-1)/t=m) : (t : ℝ) ∈ Icc (bandLeft p m) (bandRight p m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqlo : m*t ≤ p-1 := by rw [← he]; exact Nat.div_mul_le_self _ _
  have hqhi : p-1 < (m+1)*t := by
    rw [← he]
    exact (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_succ_self ((p-1)/t))
  constructor
  · unfold bandLeft
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < m+1)).mpr
    have hR : ((p-1 : ℕ) : ℝ) < ((m : ℝ)+1)*t := by exact_mod_cast hqhi
    nlinarith
  · unfold bandRight
    apply (le_div_iff₀ hmR).mpr
    have hR : (m : ℝ)*t ≤ ((p-1 : ℕ) : ℝ) := by exact_mod_cast hqlo
    nlinarith

/-- Title: `Every conductor above the square-root cutoff has a quotient whose square is at most p`. -/
theorem large_conductor_quotient_square {p t : ℕ} (ht : Nat.sqrt p < t) :
    ((p-1)/t)^2 ≤ p := by
  have htpos : 0 < t := by omega
  have hsq := Nat.lt_succ_sqrt' p
  simp only [Nat.succ_eq_add_one] at hsq
  have hmul : (Nat.sqrt p+1)^2 ≤ (Nat.sqrt p+1)*t := by
    have hs : Nat.sqrt p+1 ≤ t := by omega
    nlinarith
  have hlt : (p-1)/t < Nat.sqrt p+1 :=
    (Nat.div_lt_iff_lt_mul htpos).mpr (by omega)
  exact Nat.le_sqrt'.mp (by omega)

/-- Title: `The actual three-phase bound holds on every retained consecutive conductor set`. -/
theorem retained_band_bound {p m u v j : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hmsq : m^2 ≤ p) (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (S : Finset ℕ)
    (hconv : ∀ i ∈ S, ∀ k ∈ S, ∀ t, i ≤ t → t ≤ k → t ∈ S)
    (hS : ∀ t ∈ S, (t : ℝ) ∈ Icc (bandLeft p m) (bandRight p m) ∧
      2*u < t ∧ 2*v < t ∧ 2*j < t) :
    |∑ t ∈ S, originalFrequency p t u v j| ≤
      291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j := by
  by_cases he : S.Nonempty
  · let a := S.min' he
    let b := S.max' he
    have hab : a ≤ b := S.min'_le _ (S.max'_mem he)
    have ha := hS a (S.min'_mem he)
    have hb := hS b (S.max'_mem he)
    have hcast : (a : ℝ)+((b-a : ℕ) : ℝ) = b := by rw [Nat.cast_sub hab]; ring
    have hsub : Icc (a : ℝ) (a+(b-a : ℕ)) ⊆ Icc (bandLeft p m) (bandRight p m) := by
      rw [hcast]
      intro x hx
      exact ⟨ha.1.1.trans hx.1, hx.2.trans hb.1.2⟩
    have hh := frequency_band_bound hp hm hmsq hu hup hv hj ha.2.1 ha.2.2.1 ha.2.2.2 hsub
    have hsum : (∑ t ∈ S, originalFrequency p t u v j) = frequencyBandSum p u v j a (b-a) := by
      rw [consecutive_finset_eq_Icc S he hconv]
      change (∑ t ∈ Finset.Icc a b, originalFrequency p t u v j) = _
      have hset : Finset.Icc a b = Finset.Ico a (b+1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range, show b+1-a=b-a+1 by omega]
      simpa only [Nat.add_comm] using original_frequency_interval p u v j a (b-a)
    rwa [hsum]
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (bandSummandScale_nonneg p m u v j hu)

end NField.Alignment.CommonResetRetainedBands
