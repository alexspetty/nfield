/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetRootSums
import NField.Alignment.CompletedPrefixDivisorGrowth

/-! # The two literal gcd-weighted inverse-frequency sums -/

noncomputable section

namespace NField.Alignment.CommonResetDivisorSums

open scoped BigOperators
open CommonResetRootSums CommonResetSmallConductors DedekindInverseResidueTransform

theorem sum_multiples {R : Type*} [AddCommMonoid R] (F : ℕ → R) (Y : ℕ)
    {d : ℕ} (hd : 0 < d) :
    (∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), F u) =
      ∑ k ∈ Finset.Icc 1 (Y/d), F (d*k) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => d*k)
  · intro k hk
    have hkI := Finset.mem_Icc.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right d k⟩
    calc
      d*k ≤ d*(Y/d) := Nat.mul_le_mul_left d hkI.2
      _ ≤ Y := Nat.mul_div_le Y d
  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro u hu
    have huD := Finset.mem_filter.mp hu
    have huI := Finset.mem_Icc.mp huD.1
    refine ⟨u/d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right huI.2⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd huI.1 huD.2) hd
    · exact Nat.mul_div_cancel' huD.2
  · intro k hk
    rfl

theorem sqrt_gcd_divisor_expansion {a : ℕ} (ha : 0 < a) (u : ℕ) :
    Real.sqrt (a.gcd u : ℝ) ≤ ∑ d ∈ a.divisors, if d ∣ u then Real.sqrt (d : ℝ) else 0 := by
  have hg : a.gcd u ∈ a.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left a u, ha.ne'⟩
  have hb := Finset.single_le_sum
    (s := a.divisors) (f := fun d : ℕ => if d ∣ u then Real.sqrt (d : ℝ) else 0)
    (fun d _ => by split_ifs <;> positivity) hg
  simpa only [if_pos (Nat.gcd_dvd_right a u)] using hb

theorem gcd_weight_divisor_expansion {a : ℕ} (ha : 0 < a) (Y : ℕ) (w : ℕ → ℝ)
    (hw : ∀ u, 0 ≤ w u) :
    (∑ u ∈ Finset.Icc 1 Y, Real.sqrt (a.gcd u : ℝ)*w u) ≤
      ∑ d ∈ a.divisors, Real.sqrt (d : ℝ)*∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), w u := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 Y, (∑ d ∈ a.divisors, if d ∣ u then Real.sqrt (d : ℝ) else 0)*w u := by
      exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (sqrt_gcd_divisor_expansion ha u) (hw u))
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hd : d ∣ u <;> simp only [hd, if_true, if_false, zero_mul]

theorem harmonic_multiples_bound (Y : ℕ) {d : ℕ} (hd : 0 < d) :
    Real.sqrt (d : ℝ)*(∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), 1/(u : ℝ)) ≤
      (harmonic Y : ℝ)/Real.sqrt (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hds := Real.sq_sqrt hdR.le
  have hds0 := (Real.sqrt_pos.mpr hdR).ne'
  rw [sum_multiples _ Y hd]
  calc
    _ = (harmonic (Y/d) : ℝ)/Real.sqrt (d : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := (Finset.mem_Icc.mp hk).1; omega)
      push_cast
      field_simp
      nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right (harmonic_monotone (Nat.div_le_self Y d)) (Real.sqrt_nonneg _)

theorem root_multiples_bound (Y : ℕ) {d : ℕ} (hd : 0 < d) :
    Real.sqrt (d : ℝ)*(∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), 1/Real.sqrt (u : ℝ)) ≤
      2*Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hds0 := (Real.sqrt_pos.mpr hdR).ne'
  rw [sum_multiples _ Y hd]
  have hdiv : ((Y/d : ℕ) : ℝ) ≤ (Y : ℝ)/(d : ℝ) := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self Y d
  calc
    _ = ∑ k ∈ Finset.Icc 1 (Y/d), 1/Real.sqrt (k : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      rw [Real.sqrt_mul hdR.le]
      field_simp
    _ ≤ 2*Real.sqrt ((Y/d : ℕ) : ℝ) := sum_reciprocal_sqrt _
    _ ≤ 2*Real.sqrt ((Y : ℝ)/(d : ℝ)) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdiv) (by norm_num)
    _ = _ := by rw [Real.sqrt_div (Nat.cast_nonneg Y)]; ring

/-- Title: `The complete reciprocal inverse-frequency sum has its exact divisor expansion bound`. -/
theorem gcd_harmonic_sum {a : ℕ} (ha : 0 < a) (Y : ℕ) :
    (∑ u ∈ Finset.Icc 1 Y, Real.sqrt (a.gcd u : ℝ)/(u : ℝ)) ≤
      (harmonic Y : ℝ)*reciprocalSqrtDivisorSum a := by
  have hb := gcd_weight_divisor_expansion ha Y (fun u => 1/(u : ℝ)) (fun u => by positivity)
  simp only [mul_one_div] at hb
  calc
    _ ≤ ∑ d ∈ a.divisors, Real.sqrt (d : ℝ)*∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), 1/(u : ℝ) := hb
    _ ≤ ∑ d ∈ a.divisors, (harmonic Y : ℝ)/Real.sqrt (d : ℝ) :=
      Finset.sum_le_sum (fun d hd => harmonic_multiples_bound Y (Nat.pos_of_mem_divisors hd))
    _ = _ := by unfold reciprocalSqrtDivisorSum; rw [Finset.mul_sum]; simp only [div_eq_mul_inv]

/-- Title: `The complete square-root inverse-frequency sum has its exact divisor expansion bound`. -/
theorem gcd_root_sum {a : ℕ} (ha : 0 < a) (Y : ℕ) :
    (∑ u ∈ Finset.Icc 1 Y, Real.sqrt (a.gcd u : ℝ)/Real.sqrt (u : ℝ)) ≤
      2*Real.sqrt (Y : ℝ)*reciprocalSqrtDivisorSum a := by
  have hb := gcd_weight_divisor_expansion ha Y (fun u => 1/Real.sqrt (u : ℝ)) (fun u => by positivity)
  simp only [mul_one_div] at hb
  calc
    _ ≤ ∑ d ∈ a.divisors, Real.sqrt (d : ℝ)*∑ u ∈ (Finset.Icc 1 Y).filter (fun u => d ∣ u), 1/Real.sqrt (u : ℝ) := hb
    _ ≤ ∑ d ∈ a.divisors, 2*Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ) :=
      Finset.sum_le_sum (fun d hd => root_multiples_bound Y (Nat.pos_of_mem_divisors hd))
    _ = _ := by unfold reciprocalSqrtDivisorSum; rw [Finset.mul_sum]; simp only [div_eq_mul_inv]

end NField.Alignment.CommonResetDivisorSums
