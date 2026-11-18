/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DivisorSmallPowerBound
import Mathlib
/-! # Divisor budgets for the selected forests

The triple-divisor function is defined by its actual divisor sum. Its
small-power estimate is deduced from the independently proved divisor
bound rather than supplied as an asymptotic assumption.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment.DivisorSmallPowerBound

def tripleDivisorCount (D : ℕ) : ℕ :=
  ∑ d ∈ D.divisors, d.divisors.card

theorem divisor_count_mono_dvd {d D : ℕ} (hD : D ≠ 0) (h : d ∣ D) :
    d.divisors.card ≤ D.divisors.card := by
  apply Finset.card_le_card
  intro a ha
  rw [Nat.mem_divisors] at ha ⊢
  exact ⟨ha.1.trans h, hD⟩

theorem triple_divisor_le_square (D : ℕ) :
    tripleDivisorCount D ≤ D.divisors.card^2 := by
  by_cases hD : D = 0
  · simp [hD, tripleDivisorCount]
  · calc
      tripleDivisorCount D ≤ ∑ _d ∈ D.divisors, D.divisors.card := by
        apply Finset.sum_le_sum
        intro d hd
        exact divisor_count_mono_dvd hD (Nat.mem_divisors.mp hd).1
      _ = D.divisors.card^2 := by simp [pow_two]

/-- The second assertion of Lemma8.1, uniformly for all positive D. -/
theorem triple_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 0 < D →
      (tripleDivisorCount D : ℝ) ≤ C*(D : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := divisor_count_small_power (ε/2) (by positivity)
  refine ⟨C^2, sq_pos_of_pos hC, ?_⟩
  intro D hD
  have ht : (tripleDivisorCount D : ℝ) ≤ (D.divisors.card : ℝ)^2 := by
    exact_mod_cast triple_divisor_le_square D
  calc
    (tripleDivisorCount D : ℝ) ≤ (D.divisors.card : ℝ)^2 := ht
    _ ≤ (C*(D : ℝ)^(ε/2))^2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hb D hD) 2
    _ = C^2*(D : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg D)]
      congr 1
      ring_nf

def supportedCutoff (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers N.primeFactors)

def incomingDivisorBudget (N : ℕ) : ℝ :=
  ∑ n ∈ supportedCutoff N, (n.divisors.card : ℝ)

theorem supported_cutoff_mem {N n : ℕ} (hN : N ≠ 0) :
    n ∈ supportedCutoff N ↔
      1 ≤ n ∧ n ≤ N ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ N := by
  simp only [supportedCutoff, Finset.mem_filter, Finset.mem_Icc,
    Nat.mem_factoredNumbers']
  constructor
  · rintro ⟨⟨hnpos, hnN⟩, hs⟩
    exact ⟨hnpos, hnN, fun p hp hd => (Nat.mem_primeFactors.mp (hs p hp hd)).2.1⟩
  · rintro ⟨hnpos, hnN, hs⟩
    exact ⟨⟨hnpos, hnN⟩, fun p hp hd => Nat.mem_primeFactors.mpr ⟨hp, hs p hp hd, hN⟩⟩

def negativePowerHom (δ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-δ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

def supportEulerProduct (N : ℕ) (δ : ℝ) : ℝ :=
  ∏ p ∈ N.primeFactors, (1-(p : ℝ)^(-δ))⁻¹

theorem prime_negative_power_lt_one {δ : ℝ} (hδ : 0 < δ)
    {p : ℕ} (hp : p.Prime) : (p : ℝ)^(-δ) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem supported_rpow_sum_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (s : Finset ℕ) :
    (∑ n ∈ s.filter (fun n => n ∈ Nat.factoredNumbers N.primeFactors),
      (n : ℝ)^(-δ)) ≤ supportEulerProduct N δ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖negativePowerHom δ p‖ < 1 := by
    change ‖(p : ℝ)^(-δ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact prime_negative_power_lt_one hδ hp
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePowerHom δ) (fun {_} hp => hprime hp) N.primeFactors).2
  have hf : N.primeFactors.filter Nat.Prime = N.primeFactors :=
    Finset.filter_true_of_mem fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hsum : HasSum (fun n : Nat.factoredNumbers N.primeFactors =>
      ((n : ℕ) : ℝ)^(-δ)) (supportEulerProduct N δ) := by
    simpa only [hf, negativePowerHom, MonoidHom.coe_mk, OneHom.coe_mk,
      supportEulerProduct] using h
  have hs : Summable ((Nat.factoredNumbers N.primeFactors).indicator
      (fun n : ℕ => (n : ℝ)^(-δ))) :=
    (summable_subtype_iff_indicator (s := Nat.factoredNumbers N.primeFactors)
      (f := fun n : ℕ => (n : ℝ)^(-δ))).mp hsum.summable
  have he : (∑' n : ℕ, (Nat.factoredNumbers N.primeFactors).indicator
      (fun n : ℕ => (n : ℝ)^(-δ)) n) = supportEulerProduct N δ :=
    (tsum_subtype (Nat.factoredNumbers N.primeFactors)
      (fun n : ℕ => (n : ℝ)^(-δ))).symm.trans hsum.tsum_eq
  rw [← he]
  simpa only [Finset.sum_filter, Set.indicator_apply] using
    hs.sum_le_tsum s (fun n _ => by
      simp only [Set.indicator_apply]
      split_ifs <;> positivity)

/-- A literal finite Rankin bound, for the prime support of N itself. -/
theorem supported_cutoff_rankin (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ((supportedCutoff N).card : ℝ) ≤
      (N : ℝ)^δ * supportEulerProduct N δ := by
  classical
  have hterm (n : ℕ) (hn : n ∈ supportedCutoff N) :
      (1 : ℝ) ≤ (N : ℝ)^δ * (n : ℝ)^(-δ) := by
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [Real.rpow_neg hnR.le, ← div_eq_mul_inv]
    exact (one_le_div (Real.rpow_pos_of_pos hnR _)).mpr
      (Real.rpow_le_rpow hnR.le (by exact_mod_cast hnN) hδ.le)
  calc
    ((supportedCutoff N).card : ℝ) = ∑ _n ∈ supportedCutoff N, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ supportedCutoff N, (N : ℝ)^δ * (n : ℝ)^(-δ) :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ)^δ * ∑ n ∈ supportedCutoff N, (n : ℝ)^(-δ) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ)^δ * supportEulerProduct N δ :=
      mul_le_mul_of_nonneg_left (supported_rpow_sum_le N hδ (Finset.Icc 1 N))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem prime_euler_factor_pos {δ : ℝ} (hδ : 0 < δ)
    {p : ℕ} (hp : p.Prime) : 0 < (1-(p : ℝ)^(-δ))⁻¹ :=
  inv_pos.mpr (sub_pos.mpr (prime_negative_power_lt_one hδ hp))

theorem prime_euler_factor_ge_one {δ : ℝ} (hδ : 0 < δ)
    {p : ℕ} (hp : p.Prime) : 1 ≤ (1-(p : ℝ)^(-δ))⁻¹ := by
  apply (one_le_inv₀ (sub_pos.mpr (prime_negative_power_lt_one hδ hp))).mpr
  have := Real.rpow_nonneg (Nat.cast_nonneg p) (-δ)
  nlinarith

/-- The finite support Euler product costs arbitrarily little power of N. -/
theorem support_euler_small_power (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      supportEulerProduct N δ ≤ C*(N : ℝ)^δ := by
  classical
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)^δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (ht.eventually (Filter.eventually_ge_atTop (2 : ℝ)))
  let small : Finset ℕ := (Finset.range K).filter Nat.Prime
  let factor : ℕ → ℝ := fun p => (1-(p : ℝ)^(-δ))⁻¹
  let C : ℝ := ∏ p ∈ small, factor p
  have hC : 0 < C := Finset.prod_pos fun p hp =>
    prime_euler_factor_pos hδ (Finset.mem_filter.mp hp).2
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hlocal (p : ℕ) (hp : p ∈ N.primeFactors) :
      factor p ≤ (if p < K then factor p else 1)*(p : ℝ)^δ := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpow1 : 1 ≤ (p : ℝ)^δ :=
      Real.one_le_rpow (by exact_mod_cast hprime.one_lt.le) hδ.le
    by_cases hsmall : p < K
    · rw [if_pos hsmall]
      exact le_mul_of_one_le_right (prime_euler_factor_pos hδ hprime).le hpow1
    · rw [if_neg hsmall, one_mul]
      apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr (prime_negative_power_lt_one hδ hprime))).mpr
      have hpow2 := hK p (Nat.le_of_not_lt hsmall)
      have hproduct : (p : ℝ)^δ * (p : ℝ)^(-δ) = 1 := by
        rw [Real.rpow_neg hpR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpR _).ne']
      nlinarith
  have hconstants : (∏ p ∈ N.primeFactors, if p < K then factor p else 1) ≤ C := by
    rw [← Finset.prod_filter]
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Finset.mem_filter.mp hp).2,
          Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
    · intro p hp
      exact (prime_euler_factor_pos hδ
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
    · intro p hp _
      exact prime_euler_factor_ge_one hδ (Finset.mem_filter.mp hp).2
  have hrad : (∏ p ∈ N.primeFactors, (p : ℝ)^δ) ≤ (N : ℝ)^δ := by
    rw [Real.finsetProd_rpow N.primeFactors (fun p => (p : ℝ))
      (fun p _ => Nat.cast_nonneg p) δ]
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  calc
    supportEulerProduct N δ ≤
        ∏ p ∈ N.primeFactors, (if p < K then factor p else 1)*(p : ℝ)^δ := by
      apply Finset.prod_le_prod
      · intro p hp
        exact (prime_euler_factor_pos hδ (Nat.prime_of_mem_primeFactors hp)).le
      · exact hlocal
    _ = (∏ p ∈ N.primeFactors, if p < K then factor p else 1) *
        (∏ p ∈ N.primeFactors, (p : ℝ)^δ) := Finset.prod_mul_distrib
    _ ≤ C*(N : ℝ)^δ := mul_le_mul hconstants hrad (by positivity) hC.le

/-- The first assertion of Lemma8.1, with the actual moving prime support. -/
theorem incoming_divisor_small_power (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      incomingDivisorBudget N ≤ C*(N : ℝ)^(2*η) := by
  let δ := 2*η/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := support_euler_small_power δ hδ
  obtain ⟨B, hB, hb⟩ := divisor_count_small_power δ hδ
  refine ⟨A*B, mul_pos hA hB, ?_⟩
  intro N hN
  have hcount : ((supportedCutoff N).card : ℝ) ≤ A*(N : ℝ)^(2*δ) := by
    calc
      _ ≤ (N : ℝ)^δ * supportEulerProduct N δ := supported_cutoff_rankin N hδ
      _ ≤ (N : ℝ)^δ * (A*(N : ℝ)^δ) :=
        mul_le_mul_of_nonneg_left (ha N hN) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
        exact congrArg (fun a : ℝ => A*(N : ℝ)^a) (by ring)
  calc
    incomingDivisorBudget N ≤ ∑ _n ∈ supportedCutoff N, B*(N : ℝ)^δ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      exact (hb n hnpos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN) hδ.le) hB.le)
    _ = ((supportedCutoff N).card : ℝ)*(B*(N : ℝ)^δ) := by simp
    _ ≤ (A*(N : ℝ)^(2*δ))*(B*(N : ℝ)^δ) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (A*B)*(N : ℝ)^(2*η) := by
      rw [show (A*(N : ℝ)^(2*δ))*(B*(N : ℝ)^δ) =
        (A*B)*((N : ℝ)^(2*δ)*(N : ℝ)^δ) by ring,
        ← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
      exact congrArg (fun a : ℝ => (A*B)*(N : ℝ)^a) (by dsimp [δ]; ring)

/-- Both printed budgets hold with one constant depending only on eta. -/
theorem incoming_and_triple_budget (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, 0 < N → incomingDivisorBudget N ≤ C*(N : ℝ)^(2*η)) ∧
      (∀ D : ℕ, 0 < D → (tripleDivisorCount D : ℝ) ≤ C*(D : ℝ)^η) := by
  obtain ⟨A, hA, ha⟩ := incoming_divisor_small_power η hη
  obtain ⟨B, _hB, hb⟩ := triple_divisor_small_power η hη
  refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _), ?_, ?_⟩
  · intro N hN
    exact (ha N hN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro D hD
    exact (hb D hD).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end NField.ResetForests.Core
