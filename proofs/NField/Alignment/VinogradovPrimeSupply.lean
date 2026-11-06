/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovUnrestrictedRecurrence
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniformly bounded family of separating primes

Mathlib's Chebyshev bounds supply enough primes in an interval with a
polynomial size ratio. This avoids rebuilding prime-number estimates or
using repeated Bertrand steps with an exponentially large upper endpoint.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovPrimeSupply
open scoped BigOperators Classical
open Filter Real

theorem eventually_theta_ge_linear :
    ∀ᶠ x : ℝ in atTop, Real.log 2 / 2 * x ≤ Chebyshev.theta x := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show 0 < Real.log 2 / 16 by positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), hl] with x hx hlog
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog' : Real.log x ≤ Real.log 2 / 16 * Real.sqrt x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg x)] using hlog
  have hs : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx1)
  have hsq := Real.sq_sqrt hx0
  have hshift : Real.log (x + 2) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := Real.log_pow x 2
  have hmain := Chebyshev.theta_ge' hx1
  have hsmall := mul_le_mul_of_nonneg_left hlog' (by positivity : 0 ≤ 2 * Real.sqrt x)
  have hlinear := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.log 2 / 8)
  nlinarith

def primesBetween (L U : ℕ) : Finset ℕ := Nat.primesLE U \ Nat.primesLE L

theorem mem_primesBetween {L U p : ℕ} : p ∈ primesBetween L U ↔ p.Prime ∧ L < p ∧ p ≤ U := by
  simp only [primesBetween, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hle, hp⟩, hnot⟩
    exact ⟨hp, lt_of_not_ge (fun h => hnot ⟨h, hp⟩), hle⟩
  · rintro ⟨hp, hlt, hle⟩
    exact ⟨⟨hle, hp⟩, fun h => (not_le_of_gt hlt) h.1⟩

theorem theta_sub_eq_sum_primesBetween {L U : ℕ} (hLU : L ≤ U) :
    Chebyshev.theta U - Chebyshev.theta L =
      ∑ p ∈ primesBetween L U, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  exact (Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hLU)).symm

theorem sum_log_primesBetween_le {L U : ℕ} :
    (∑ p ∈ primesBetween L U, Real.log p) ≤
      (primesBetween L U).card * (2 * Real.sqrt U) := by
  have hlog : Real.log U ≤ 2 * Real.sqrt U := by
    have h := Real.log_le_rpow_div (x := (U : ℝ)) (Nat.cast_nonneg U)
      (show 0 < (1 / 2 : ℝ) by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  calc
    _ ≤ ∑ _p ∈ primesBetween L U, 2 * Real.sqrt U := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := mem_primesBetween.mp hp
      exact (Real.log_le_log (by exact_mod_cast hm.1.pos)
        (by exact_mod_cast hm.2.2)).trans hlog
    _ = _ := by simp

/-- An absolute polynomial interval ratio supplies any requested finite number of primes. -/
theorem exists_prime_interval_constant :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ L m : ℕ, 1 ≤ L → 1 ≤ m →
      m ≤ (primesBetween L (C * m ^ 2 * L)).card := by
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_theta_ge_linear
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 A + 2 * Real.log 4 / c + 4 / c)
  have hK1 : (1 : ℝ) ≤ K := by
    have := le_max_left (1 : ℝ) A
    have : 0 < 2 * Real.log 4 / c := by positivity
    have : 0 < 4 / c := by positivity
    linarith
  have hKA : A ≤ (K : ℝ) := by
    have := le_max_right (1 : ℝ) A
    have : 0 < 2 * Real.log 4 / c := by positivity
    have : 0 < 4 / c := by positivity
    linarith
  have hcK4 : 4 ≤ c * K := by
    have hq : 4 / c < (K : ℝ) := by
      have := le_max_left (1 : ℝ) A
      have : 0 < 2 * Real.log 4 / c := by positivity
      linarith
    have := (div_lt_iff₀ hc).mp hq
    nlinarith
  have hcKlog : 2 * Real.log 4 ≤ c * K := by
    have hq : 2 * Real.log 4 / c < (K : ℝ) := by
      have := le_max_left (1 : ℝ) A
      have : 0 < 4 / c := by positivity
      linarith
    have := (div_lt_iff₀ hc).mp hq
    nlinarith
  refine ⟨K ^ 2, by exact_mod_cast (show (1 : ℝ) ≤ (K : ℝ) ^ 2 by nlinarith), ?_⟩
  intro L m hL hm
  let U := K ^ 2 * m ^ 2 * L
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hUeq : (U : ℝ) = (K : ℝ) ^ 2 * (m : ℝ) ^ 2 * L := by
    simp only [U, Nat.cast_mul, Nat.cast_pow]
  have hKm : (K : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
    calc
      _ ≤ (K : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
  have hKU : (K : ℝ) ≤ U := by
    rw [hUeq]
    exact hKm.trans (le_mul_of_one_le_right (by positivity) hLr)
  have hLU : (L : ℝ) ≤ U := by
    rw [hUeq]
    exact le_mul_of_one_le_left (by positivity) (hK1.trans hKm)
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le (by norm_num) (hK1.trans hKU)
  have htheta : c * U ≤ Chebyshev.theta U := hA U (hKA.trans hKU)
  have hupper := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg L)
  have hcoeff : 2 * Real.log 4 * L ≤ c * U := by
    calc
      _ ≤ (c * K) * L := mul_le_mul_of_nonneg_right hcKlog (by positivity)
      _ ≤ _ := by rw [hUeq]; nlinarith [mul_le_mul_of_nonneg_right hKm (show 0 ≤ c * L by positivity)]
  have hroot : (K : ℝ) * m ≤ Real.sqrt U := by
    apply (Real.le_sqrt (by positivity) (le_of_lt hU0)).mpr
    rw [hUeq]
    calc
      _ = (K : ℝ) ^ 2 * (m : ℝ) ^ 2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLr
  have hmroot : 4 * (m : ℝ) ≤ c * Real.sqrt U := by
    calc
      _ ≤ (c * K) * m := mul_le_mul_of_nonneg_right hcK4 (by positivity)
      _ = c * ((K : ℝ) * m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot hc.le
  have hmroot' := mul_le_mul_of_nonneg_right hmroot (Real.sqrt_nonneg (U : ℝ))
  have hsq := Real.sq_sqrt (le_of_lt hU0)
  have hsum := sum_log_primesBetween_le (L := L) (U := U)
  rw [← theta_sub_eq_sum_primesBetween (by exact_mod_cast hLU)] at hsum
  have hcount : (m : ℝ) * (2 * Real.sqrt U) ≤
      (primesBetween L U).card * (2 * Real.sqrt U) := by nlinarith
  have hspos : 0 < 2 * Real.sqrt U := by positivity
  have hcount' := (mul_le_mul_iff_left₀ hspos).mp hcount
  exact_mod_cast hcount'

/-- A degree-controlled prime family works simultaneously for every distinct head pair. -/
theorem exists_separating_prime_family_constant :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ H n R : ℕ, 1 ≤ n → 1 ≤ R → H ≤ R ^ n →
      ∃ P : Finset ℕ, P.card = 2 * n ^ 3 + 1 ∧
        (∀ p ∈ P, p.Prime ∧ n * R < p ∧ p ≤ C * (2 * n ^ 3 + 1) ^ 2 * (n * R)) ∧
        H ^ (2 * n ^ 2) < ∏ p ∈ P, p := by
  obtain ⟨C, hC, hsupply⟩ := exists_prime_interval_constant
  refine ⟨C, hC, ?_⟩
  intro H n R hn hR hH
  let m := 2 * n ^ 3 + 1
  let L := n * R
  have hL : 1 ≤ L := hR.trans (le_mul_of_one_le_left (Nat.zero_le _) hn)
  obtain ⟨P, hP, hcard⟩ := Finset.exists_subset_card_eq
    (hsupply L m hL (by dsimp [m]; omega))
  have hmem : ∀ p ∈ P, p.Prime ∧ n * R < p ∧ p ≤ C * m ^ 2 * (n * R) := by
    intro p hp
    exact mem_primesBetween.mp (hP hp)
  refine ⟨P, hcard, hmem, ?_⟩
  have hRle : R ≤ L := le_mul_of_one_le_left (Nat.zero_le _) hn
  have hpow : (R + 1) ^ m ≤ ∏ p ∈ P, p := by
    calc
      _ = ∏ _p ∈ P, (R + 1) := by simp only [Finset.prod_const, hcard]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => by
        have := (hmem p hp).2.1
        omega)
  calc
    H ^ (2 * n ^ 2) ≤ (R ^ n) ^ (2 * n ^ 2) := Nat.pow_le_pow_left hH _
    _ = R ^ (2 * n ^ 3) := by rw [← pow_mul]; congr 1; ring
    _ ≤ R ^ m := Nat.pow_le_pow_right hR (by dsimp [m]; omega)
    _ < (R + 1) ^ m := pow_lt_pow_left₀ (by omega) (by omega) (by dsimp [m]; omega)
    _ ≤ _ := hpow

end NField.Alignment.VinogradovPrimeSupply
