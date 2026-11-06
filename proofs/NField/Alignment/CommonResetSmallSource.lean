/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetFrequencyPartition
import NField.Alignment.CommonResetSmallConductors
import NField.Alignment.CommonResetTailGrowth

/-! # The actual small-conductor source at the published cutoff -/

noncomputable section

namespace NField.Alignment.CommonResetSmallSource

open scoped BigOperators
open CommonResetFrequencyPartition CommonResetConductorSelection CommonResetFrequencies
open CommonResetHalfFrequencies CommonResetSmallConductors CommonResetTailGrowth
open CommonResetConductor DedekindInverseResidueTransform

theorem quarterCutoff_lt {p : ℕ} (hp : 2 ≤ p) : quarterCutoff p < p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℝ)^(3/4 : ℝ) < p := by
    calc
      _ < (p : ℝ)^(1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hpR (by norm_num)
      _ = _ := Real.rpow_one _
  have hK : (quarterCutoff p : ℝ) ≤ (p : ℝ)^(3/4 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  exact_mod_cast hK.trans_lt hpow

theorem quarterCutoff_product {p : ℕ} (hp : 1 ≤ p) :
    (quarterCutoff p : ℝ)*((quarterCutoff p : ℝ)+1) ≤ 2*(p : ℝ)^(3/2 : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : 1 ≤ (p : ℝ)^(3/4 : ℝ) := Real.one_le_rpow hpR (by norm_num)
  have hK : (quarterCutoff p : ℝ) ≤ (p : ℝ)^(3/4 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  calc
    _ ≤ ((p : ℝ)^(3/4 : ℝ))*(2*(p : ℝ)^(3/4 : ℝ)) := by gcongr <;> linarith
    _ = _ := by
      rw [show (p : ℝ)^(3/4 : ℝ)*(2*(p : ℝ)^(3/4 : ℝ)) = 2*((p : ℝ)^(3/4 : ℝ))^2 by ring]
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      norm_num

theorem completeFrequencies_terminal {N q t : ℕ} (ht : 2 ≤ t) (hq : q.Coprime t) :
    completeFrequencies N q t = (2*(harmonic (N/t) : ℝ)/(t : ℝ))*
      ∑ a ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*a) := by
  letI : NeZero t := ⟨by omega⟩
  rw [← completedConductor_eq_frequencies, completedConductor, dif_pos ht]
  have he := completed_half_kernel ht hq (N%t) (Nat.mod_lt N (by omega))
  rw [← he]
  ring

theorem smallSource_abs_le {p K : ℕ} (hp : p.Prime) (hK : K < p) :
    |smallSource p K| ≤ smallConductorSource (p-1) (p^2) K := by
  have hset : (Finset.Icc 2 (p-1)).filter (fun t => t≤K) = Finset.Icc 2 K := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  unfold smallSource
  rw [← Finset.sum_filter, hset]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold smallConductorSource
  apply Finset.sum_le_sum
  intro t ht
  rw [completeFrequencies_terminal (Finset.mem_Icc.mp ht).1
    (prime_square_coprime_below hp (by have := (Finset.mem_Icc.mp ht).1; omega)
      ((Finset.mem_Icc.mp ht).2.trans_lt hK))]

/-- Title: `All original frequencies at the published small-conductor cutoff cost at most three harmonic factors`. -/
theorem small_source_finite_bound {p : ℕ} (hp : p.Prime) :
    |smallSource p (quarterCutoff p)| ≤ (harmonic p : ℝ)^3*(p : ℝ)^(3/2 : ℝ) := by
  have hK := quarterCutoff_lt hp.two_le
  have hbound := small_conductor_bound (p-1) (p^2) (quarterCutoff p) (fun t ht =>
    prime_square_coprime_below hp (by have := (Finset.mem_Icc.mp ht).1; omega)
      ((Finset.mem_Icc.mp ht).2.trans_lt hK))
  have hH := harmonic_nonneg p
  have hHKn := harmonic_nonneg (quarterCutoff p)
  have hHK := harmonic_monotone hK.le
  have hHN := harmonic_monotone (Nat.sub_le p 1)
  have hprod := quarterCutoff_product hp.one_le
  calc
    _ ≤ smallConductorSource (p-1) (p^2) (quarterCutoff p) := smallSource_abs_le hp hK
    _ ≤ (harmonic (p-1) : ℝ)*(quarterCutoff p : ℝ)*((quarterCutoff p : ℝ)+1)*
        (harmonic (quarterCutoff p) : ℝ)^2/8 := hbound
    _ = (harmonic (p-1) : ℝ)*((quarterCutoff p : ℝ)*((quarterCutoff p : ℝ)+1))*
        (harmonic (quarterCutoff p) : ℝ)^2/8 := by ring
    _ ≤ (harmonic p : ℝ)*(2*(p : ℝ)^(3/2 : ℝ))*(harmonic p : ℝ)^2/8 := by
      gcongr
    _ ≤ _ := by
      have hcost : 0 ≤ (harmonic p : ℝ)^3*(p : ℝ)^(3/2 : ℝ) := by positivity
      nlinarith

/-- Title: `The full small-conductor source satisfies the published three-halves-plus-epsilon bound`. -/
theorem small_source_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      |smallSource p (quarterCutoff p)| ≤ C*(p : ℝ)^(3/2+ε) := by
  let C : ℝ := (1+1/(ε/3))^3
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p hp
  have hH := harmonic_small_power (ε/3) (by positivity) hp.one_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    _ ≤ (harmonic p : ℝ)^3*(p : ℝ)^(3/2 : ℝ) := small_source_finite_bound hp
    _ ≤ ((1+1/(ε/3))*(p : ℝ)^(ε/3))^3*(p : ℝ)^(3/2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (harmonic_nonneg _) hH 3) (Real.rpow_nonneg hpR.le _)
    _ = _ := by
      rw [mul_pow]
      dsimp [C]
      rw [mul_assoc, ← Real.rpow_mul_natCast hpR.le, ← Real.rpow_add hpR]
      congr 2
      ring

end NField.Alignment.CommonResetSmallSource
