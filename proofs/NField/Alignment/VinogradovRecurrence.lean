/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovPrimeSupply

/-!
# The unconditional finite Vinogradov recurrence

For every interval, degree, and positive tail length, a prime at the
degree-root scale gives a shorter-interval moment bound. All costs are
explicit except for one absolute constant supplied by Mathlib's Chebyshev
estimates. No mean-value estimate or prime-density hypothesis is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovRecurrence
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovUnrestrictedRecurrence VinogradovPrimeSupply

def rootCeil (H n : ℕ) : ℕ := ⌈(H : ℝ) ^ ((n : ℝ)⁻¹)⌉₊

theorem rootCeil_pos {H n : ℕ} (hH : 1 ≤ H) : 1 ≤ rootCeil H n := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < H by omega)) _

theorem le_rootCeil_pow {H n : ℕ} (hn : 1 ≤ n) : H ≤ rootCeil H n ^ n := by
  have hr : (H : ℝ) ^ ((n : ℝ)⁻¹) ≤ (rootCeil H n : ℝ) := Nat.le_ceil _
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg H) _) hr n
  rw [Real.rpow_inv_natCast_pow (Nat.cast_nonneg H) (by omega)] at hpow
  exact_mod_cast hpow

theorem rootCeil_le_two_mul_root {H n : ℕ} (hH : 1 ≤ H) :
    (rootCeil H n : ℝ) ≤ 2 * (H : ℝ) ^ ((n : ℝ)⁻¹) := by
  have hr : (1 : ℝ) ≤ (H : ℝ) ^ ((n : ℝ)⁻¹) :=
    Real.one_le_rpow (by exact_mod_cast hH) (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg H) ((n : ℝ)⁻¹))
  change (rootCeil H n : ℝ) < (H : ℝ) ^ ((n : ℝ)⁻¹) + 1 at hc
  linarith

/-- Outside the unit interval, the selected prime makes the quotient interval strictly shorter. -/
theorem quotientInterval_lt {H n R p : ℕ} (hH : 2 ≤ H) (hn : 1 ≤ n)
    (hR : 1 ≤ R) (hHR : H ≤ R ^ n) (hp : n * R < p) : H / p + 1 < H := by
  have hnR : n ≤ n * R := le_mul_of_one_le_right (Nat.zero_le _) hR
  have hRn : R ≤ n * R := le_mul_of_one_le_left (Nat.zero_le _) hn
  have hp3 : 3 ≤ p := by
    by_contra h
    have hn1 : n = 1 := by omega
    have hR1 : R = 1 := by omega
    simp only [hn1, hR1, one_pow] at hHR
    omega
  have hd : H / p ≤ H / 3 := Nat.div_le_div_left hp3 (by omega)
  omega

/-- The full recurrence with a chosen integral root bound and an absolute prime-supply constant. -/
theorem exists_bounded_prime_recurrence_constant :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ H n s R : ℕ, 1 ≤ H → 1 ≤ n → 0 < s → 1 ≤ R → H ≤ R ^ n →
      ∃ p : ℕ, p.Prime ∧ n * R < p ∧ p ≤ C * (2 * n ^ 3 + 1) ^ 2 * (n * R) ∧
        momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n ≤
          2 * H ^ (n + s + (n - 1)) * (n - 1) ^ (n + s) +
            (n + s) ^ (2 * n) * (2 * n ^ 3 + 1) *
              (n.factorial * H ^ n * p ^ (2 * s + n * (n - 1) / 2) *
                momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n) := by
  obtain ⟨C, hC, hfamily⟩ := exists_separating_prime_family_constant
  refine ⟨C, hC, ?_⟩
  intro H n s R hH hn hs hR hHR
  obtain ⟨P, hcard, hmem, hprod⟩ := hfamily H n R hn hR hHR
  have hnR : n ≤ n * R := le_mul_of_one_le_right (Nat.zero_le _) hR
  have hRR : R ≤ n * R := le_mul_of_one_le_left (Nat.zero_le _) hn
  have hrec := momentCount_le_prime_family hH hn hs P
    (fun p hp => (hmem p hp).1)
    (fun p hp => hnR.trans_lt (hmem p hp).2.1)
    (fun p hp => hHR.trans (Nat.pow_le_pow_left (hRR.trans (hmem p hp).2.1.le) n)) hprod
  let f (p : ℕ) := n.factorial * H ^ n * p ^ (2 * s + n * (n - 1) / 2) *
    momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image f (Finset.card_pos.mp (by rw [hcard]; omega))
  refine ⟨p, (hmem p hp).1, (hmem p hp).2.1, (hmem p hp).2.2, ?_⟩
  have hsum : ∑ q ∈ P, f q ≤ (2 * n ^ 3 + 1) * f p := by
    calc
      _ ≤ ∑ _q ∈ P, f p := Finset.sum_le_sum hmax
      _ = _ := by simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_id]
  calc
    _ ≤ _ := hrec
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left ((n + s) ^ (2 * n)) hsum) _
    _ = _ := by simp only [f, mul_assoc]

/-- Unconditional full-count recurrence at the degree-root scale, with no prime-family premise. -/
theorem full_recurrence :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ H n s : ℕ, 1 ≤ H → 1 ≤ n → 0 < s →
      ∃ p : ℕ, p.Prime ∧ n * rootCeil H n < p ∧
        p ≤ C * (2 * n ^ 3 + 1) ^ 2 * (n * rootCeil H n) ∧
        (2 ≤ H → H / p + 1 < H) ∧
        momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n ≤
          2 * H ^ (n + s + (n - 1)) * (n - 1) ^ (n + s) +
            (n + s) ^ (2 * n) * (2 * n ^ 3 + 1) *
              (n.factorial * H ^ n * p ^ (2 * s + n * (n - 1) / 2) *
                momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n) := by
  obtain ⟨C, hC, hrec⟩ := exists_bounded_prime_recurrence_constant
  refine ⟨C, hC, ?_⟩
  intro H n s hH hn hs
  obtain ⟨p, hp, hpL, hpU, hbound⟩ :=
    hrec H n s (rootCeil H n) hH hn hs (rootCeil_pos hH) (le_rootCeil_pow hn)
  exact ⟨p, hp, hpL, hpU,
    fun hH2 => quotientInterval_lt hH2 hn (rootCeil_pos hH) (le_rootCeil_pow hn) hpL,
    hbound⟩

end NField.Alignment.VinogradovRecurrence
