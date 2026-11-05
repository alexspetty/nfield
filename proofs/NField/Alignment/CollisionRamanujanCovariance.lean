/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRamanujan
import NField.Alignment.CollisionDivisibilityCovariance
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Absolutely convergent Ramanujan covariance

Finite primitive regrouping is passed to the actual Haar increment by
norm convergence. Its conductor series is dominated by the already proved
Jordan energy, so no formal interchange of divergent sums is used.
-/

noncomputable section

namespace NField.Alignment.CollisionRamanujanCovariance

open scoped BigOperators
open Filter MeasureTheory
open CollisionRamanujan CollisionDivisibilityCovariance CollisionOdometerRecurrence
open CollisionPotentialCoboundary CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionJordanVariance CollisionMassReadout CollisionRemainderDynamics

def finiteCovarianceCoefficient (M : ℕ) (h : ℤ) (q : ℕ) : ℝ :=
  if 2 ≤ q then (finiteAmplitude collisionWeight q M)^2 * ramanujan q h else 0

def covarianceCoefficient (h : ℤ) (q : ℕ) : ℝ :=
  if 2 ≤ q then (amplitude q)^2 * ramanujan q h else 0

theorem finiteCovarianceCoefficient_bound (M : ℕ) (h : ℤ) (q : ℕ) :
    ‖finiteCovarianceCoefficient M h q‖ ≤ conductorEnergy q := by
  unfold finiteCovarianceCoefficient conductorEnergy
  split_ifs with hq
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha := pow_le_pow_left₀ (finiteAmplitude_nonneg q M) (finiteAmplitude_le_amplitude q M) 2
    calc
      _ ≤ (amplitude q)^2 * ‖ramanujan q h‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ (amplitude q)^2 * jordanTwo q :=
        mul_le_mul_of_nonneg_left ((ramanujan_norm_le q h).trans (jordanTwo_linear_lower hq))
          (sq_nonneg _)
      _ = _ := by ring
  · simp

theorem covarianceCoefficient_bound (h : ℤ) (q : ℕ) :
    ‖covarianceCoefficient h q‖ ≤ conductorEnergy q := by
  unfold covarianceCoefficient conductorEnergy
  split_ifs with hq
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := mul_le_mul_of_nonneg_left
      ((ramanujan_norm_le q h).trans (jordanTwo_linear_lower hq)) (sq_nonneg (amplitude q))
    simpa only [mul_comm] using hb
  · simp

theorem covarianceCoefficient_summable (h : ℤ) : Summable (covarianceCoefficient h) :=
  Summable.of_norm_bounded conductorEnergy_summable (covarianceCoefficient_bound h)

theorem covarianceCoefficient_norm_summable (h : ℤ) : Summable (fun q => ‖covarianceCoefficient h q‖) :=
  Summable.of_nonneg_of_le (fun _q => norm_nonneg _) (covarianceCoefficient_bound h)
    conductorEnergy_summable

theorem finiteCovarianceCoefficient_tendsto (h : ℤ) (q : ℕ) :
    Tendsto (fun M => finiteCovarianceCoefficient M h q) atTop (nhds (covarianceCoefficient h q)) := by
  unfold finiteCovarianceCoefficient covarianceCoefficient
  split_ifs
  · exact ((finiteAmplitude_tendsto q).pow 2).mul_const _
  · exact tendsto_const_nhds

theorem finiteCovarianceCoefficient_support (M : ℕ) (h : ℤ) (q : ℕ)
    (hq : q ∉ Finset.Icc 2 M) : finiteCovarianceCoefficient M h q = 0 := by
  unfold finiteCovarianceCoefficient
  split_ifs with hq2
  · have hz : finiteAmplitude collisionWeight q M = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkp := Finset.mem_Icc.mp hk
      have hqk : ¬ q ∣ k := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < k) hd
        exact hq (Finset.mem_Icc.mpr ⟨hq2, by omega⟩)
      exact if_neg hqk
    rw [hz, sq, mul_zero, zero_mul]
  · rfl

theorem finiteCovarianceCoefficient_tsum (M : ℕ) (h : ℤ) :
    (∑' q, finiteCovarianceCoefficient M h q) =
      ∑ q ∈ Finset.Icc 2 M, (finiteAmplitude collisionWeight q M)^2 * ramanujan q h := by
  have hs : HasSum (finiteCovarianceCoefficient M h)
      (∑ q ∈ Finset.Icc 2 M, finiteCovarianceCoefficient M h q) :=
    hasSum_sum_of_ne_finset_zero (finiteCovarianceCoefficient_support M h)
  rw [hs.tsum_eq]
  apply Finset.sum_congr rfl
  intro q hq
  exact if_pos (Finset.mem_Icc.mp hq).1

theorem covarianceCoefficient_limit (h : ℤ) :
    Tendsto (fun M => ∑' q, finiteCovarianceCoefficient M h q) atTop
      (nhds (∑' q, covarianceCoefficient h q)) :=
  tendsto_tsum_of_dominated_convergence conductorEnergy_summable
    (finiteCovarianceCoefficient_tendsto h)
    (Filter.Eventually.of_forall (fun M q => finiteCovarianceCoefficient_bound M h q))

theorem gcd_ramanujan_expansion {k l M : ℕ} (hk : k ∈ Finset.Icc 2 M)
    (_hl : l ∈ Finset.Icc 2 M) (h : ℤ) :
    (if (k.gcd l : ℤ) ∣ h then (k.gcd l : ℝ) else 0) - 1 =
      ∑ q ∈ Finset.Icc 2 M, if q ∣ k ∧ q ∣ l then ramanujan q h else 0 := by
  have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  have hgpos := Nat.gcd_pos_of_pos_left l hkpos
  have he : (Finset.Icc 2 M).filter (fun q => q ∣ k ∧ q ∣ l) =
      (k.gcd l).divisors.erase 1 := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq, _⟩, hqk, hql⟩
      exact ⟨by omega, Nat.dvd_gcd hqk hql, hgpos.ne'⟩
    · rintro ⟨hq1, hqd, _⟩
      have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqd hgpos
      have hqM := (Nat.le_of_dvd hgpos hqd).trans
        ((Nat.gcd_le_left l hkpos).trans (Finset.mem_Icc.mp hk).2)
      exact ⟨⟨by omega, hqM⟩, Nat.dvd_gcd_iff.mp hqd⟩
  rw [← Finset.sum_filter, he]
  have hs := Finset.sum_erase_add (k.gcd l).divisors (fun q => ramanujan q h)
    (Nat.one_mem_divisors.mpr hgpos.ne')
  rw [ramanujan_divisors hgpos, ramanujan_one] at hs
  linarith

theorem arithmeticCovarianceTerm_gcd {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (h : ℤ) :
    arithmeticCovarianceTerm h (k,l) = collisionWeight k * collisionWeight l *
      ((if (k.gcd l : ℤ) ∣ h then (k.gcd l : ℝ) else 0) - 1) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hLR : (k.lcm l : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hk hl).ne'
  have he : (k.gcd l : ℝ)*(k.lcm l : ℝ) = (k : ℝ)*(l : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm k l
  have hr : (k : ℝ)*(l : ℝ) * (if (k.gcd l : ℤ) ∣ h then 1/(k.lcm l : ℝ) else 0) =
      if (k.gcd l : ℤ) ∣ h then (k.gcd l : ℝ) else 0 := by
    split_ifs
    · field_simp
      nlinarith [he]
    · simp
  have hc : (k : ℝ)*(l : ℝ)*(1/((k : ℝ)*(l : ℝ))) = 1 := by field_simp
  unfold arithmeticCovarianceTerm
  calc
    _ = collisionWeight k * collisionWeight l *
        ((k : ℝ)*(l : ℝ)*(if (k.gcd l : ℤ) ∣ h then 1/(k.lcm l : ℝ) else 0) -
          (k : ℝ)*(l : ℝ)*(1/((k : ℝ)*(l : ℝ)))) := by ring
    _ = _ := by rw [hr, hc]

theorem finite_arithmetic_regrouping (M : ℕ) (h : ℤ) :
    (∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M, arithmeticCovarianceTerm h (k,l)) =
      ∑ q ∈ Finset.Icc 2 M, (finiteAmplitude collisionWeight q M)^2 * ramanujan q h := by
  calc
    _ = ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M, ∑ q ∈ Finset.Icc 2 M,
        collisionWeight k * collisionWeight l *
          (if q ∣ k ∧ q ∣ l then ramanujan q h else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [arithmeticCovarianceTerm_gcd (by have := (Finset.mem_Icc.mp hk).1; omega)
        (by have := (Finset.mem_Icc.mp hl).1; omega), gcd_ramanujan_expansion hk hl h,
        Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 2 M, ∑ q ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
        collisionWeight k * collisionWeight l *
          (if q ∣ k ∧ q ∣ l then ramanujan q h else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
        collisionWeight k * collisionWeight l *
          (if q ∣ k ∧ q ∣ l then ramanujan q h else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [finiteAmplitude, pow_two, Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hk : q ∣ k <;> by_cases hl : q ∣ l <;> simp [hk, hl, mul_comm]

def finiteCenteredReset (M : ℕ) : HaarL2 := ∑ k ∈ Finset.Icc 2 M, centeredResetVector k

theorem finiteCenteredReset_tendsto :
    Tendsto finiteCenteredReset atTop (nhds (∑' k, centeredResetVector k)) := by
  have he (M : ℕ) : (∑ k ∈ Finset.range (M+1), centeredResetVector k) = finiteCenteredReset M := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hn
      have hkn := Finset.mem_range.mp hk
      have hk2 : k < 2 := by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega
      interval_cases k <;> simp
  simpa only [Function.comp_def, he] using
    centeredReset_summable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem finiteCenteredReset_covariance (M h : ℕ) :
    inner ℝ (finiteCenteredReset M) (shift (-(h : ℤ)) (finiteCenteredReset M)) =
      ∑' q, finiteCovarianceCoefficient M (h : ℤ) q := by
  rw [finiteCovarianceCoefficient_tsum, ← finite_arithmetic_regrouping]
  simp only [finiteCenteredReset, map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact divisorCovarianceTerm_nat h (k,l)

theorem infiniteCenteredReset_covariance (h : ℕ) :
    inner ℝ (∑' k, centeredResetVector k) (shift (-(h : ℤ)) (∑' k, centeredResetVector k)) =
      ∑' q, covarianceCoefficient (h : ℤ) q := by
  have hl := Filter.Tendsto.inner (𝕜 := ℝ) finiteCenteredReset_tendsto
    (((shift (-(h : ℤ))).continuous.tendsto _).comp finiteCenteredReset_tendsto)
  have hr := covarianceCoefficient_limit (h : ℤ)
  simp only [Function.comp_def, finiteCenteredReset_covariance] at hl
  exact tendsto_nhds_unique hl hr

theorem incrementCovariance_ramanujan_nat (h : ℕ) :
    incrementCovariance (h : ℤ) = (4/9 : ℝ) * ∑' q, covarianceCoefficient (h : ℤ) q := by
  rw [incrementCovariance_even (h : ℤ), incrementCovariance_series, divisorCovarianceTerm_tsum,
    infiniteCenteredReset_covariance]

theorem covarianceCoefficient_even (h : ℤ) (q : ℕ) :
    covarianceCoefficient (-h) q = covarianceCoefficient h q := by
  simp only [covarianceCoefficient, ramanujan, dvd_neg]

theorem incrementCovariance_ramanujan (h : ℤ) :
    incrementCovariance h = (4/9 : ℝ) * ∑' q, covarianceCoefficient h q := by
  by_cases hh : 0 ≤ h
  · simpa only [Int.toNat_of_nonneg hh] using incrementCovariance_ramanujan_nat h.toNat
  · have he : h = -(((-h).toNat : ℕ) : ℤ) := by omega
    rw [he, incrementCovariance_even, neg_neg]
    simp_rw [covarianceCoefficient_even]
    exact incrementCovariance_ramanujan_nat (-h).toNat

def complexCovarianceCoefficient (h : ℤ) (q : ℕ) : ℂ :=
  if 2 ≤ q then (amplitude q : ℂ)^2 * primitiveSum q h else 0

theorem complexCovarianceCoefficient_eq (h : ℤ) (q : ℕ) :
    complexCovarianceCoefficient h q = (covarianceCoefficient h q : ℂ) := by
  unfold complexCovarianceCoefficient covarianceCoefficient
  rw [primitiveSum_eq_ramanujan]
  split_ifs <;> push_cast <;> rfl

theorem complexCovarianceCoefficient_norm_summable (h : ℤ) :
    Summable (fun q => ‖complexCovarianceCoefficient h q‖) := by
  simpa only [complexCovarianceCoefficient_eq, Complex.norm_real] using
    covarianceCoefficient_norm_summable h

theorem incrementCovariance_primitive (h : ℤ) :
    (incrementCovariance h : ℂ) = (4/9 : ℂ) * ∑' q, complexCovarianceCoefficient h q := by
  simp_rw [complexCovarianceCoefficient_eq]
  rw [← Complex.ofReal_tsum, incrementCovariance_ramanujan]
  push_cast
  rfl

theorem covariance_and_recurrence :
    (∀ h : ℤ, incrementCovariance h =
      (4/9 : ℝ) * ∑' k, ∑' l, arithmeticCovarianceTerm h (k,l)) ∧
    (∀ h : ℤ, Summable (arithmeticCovarianceTerm h)) ∧
    (∀ h : ℤ, (incrementCovariance h : ℂ) =
      (4/9 : ℂ) * ∑' q, complexCovarianceCoefficient h q) ∧
    (∀ h : ℤ, Summable (fun q => ‖complexCovarianceCoefficient h q‖)) ∧
    0 < incrementCovariance 0 ∧ incrementCovariance 1 < 0 ∧
    Tendsto (fun M => incrementCovariance (cutoffPeriod M : ℤ)) atTop
      (nhds (incrementCovariance 0)) ∧
    (fun M : ℕ => shift (cutoffPeriod M : ℤ) collisionPotential - collisionPotential)
      =O[atTop] (fun M : ℕ => Real.log (2 * (M : ℝ)) / Real.sqrt (M : ℝ)) := by
  exact ⟨incrementCovariance_arithmetic, arithmeticCovarianceTerm_summable,
    incrementCovariance_primitive, complexCovarianceCoefficient_norm_summable,
    incrementCovariance_zero_pos, incrementCovariance_one_neg,
    incrementCovariance_recurrence, potential_recurrence_isBigO⟩

end NField.Alignment.CollisionRamanujanCovariance
