/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovRecurrence

/-!
# Normalizing the finite Vinogradov recurrence

The degree weight is kept integral. All cancellation of interval and prime
powers is proved explicitly before the uniform mean-value induction.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovNormalizedRecurrence
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovRecurrence

def weight (n : ℕ) : ℕ := n * (n + 1) / 2
def exponent (s n : ℕ) : ℕ := 2 * s - weight n
def mean (s n H : ℕ) : ℝ :=
  (momentCount (Finset.Icc 1 (H : ℤ)) s n : ℝ) / (H : ℝ) ^ exponent s n

theorem two_mul_weight (n : ℕ) : 2 * weight n = n * (n + 1) := by
  exact Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one n)

theorem weight_le_sq {n : ℕ} (hn : 1 ≤ n) : weight n ≤ n ^ 2 := by
  have := two_mul_weight n
  nlinarith

theorem weight_add_triangle {n : ℕ} (hn : 1 ≤ n) :
    weight n + n * (n - 1) / 2 = n ^ 2 := by
  have h₁ := two_mul_weight n
  have h₂ : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n)
  have h₃ := Nat.sub_add_cancel hn
  nlinarith

theorem weight_le_pred_mul {n : ℕ} (hn : 2 ≤ n) : weight n ≤ (n - 1) * (n + 1) := by
  have h₁ := two_mul_weight n
  have h₂ : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  nlinarith

theorem exponent_identities {n s : ℕ} (hn : 1 ≤ n) (hs : n ^ 2 ≤ s) :
    exponent (n + s) n = exponent s n + 2 * n ∧
    2 * s + n * (n - 1) / 2 = exponent s n + n ^ 2 ∧
    n + s + (n - 1) ≤ exponent (n + s) n := by
  have hK := (weight_le_sq hn).trans hs
  have htri := weight_add_triangle hn
  unfold exponent
  omega

theorem momentCount_le_all_pairs (H s n : ℕ) :
    momentCount (Finset.Icc 1 (H : ℤ)) s n ≤ H ^ (2 * s) := by
  rw [momentCount_eq_pair_count]
  calc
    _ ≤ (Finset.univ : Finset
      (IntegerTuple (Finset.Icc 1 (H : ℤ)) s × IntegerTuple (Finset.Icc 1 (H : ℤ)) s)).card :=
        Finset.card_filter_le _ _
    _ = _ := by simp [IntegerTuple, two_mul, pow_add]

theorem mean_nonneg (s n H : ℕ) : 0 ≤ mean s n H := by unfold mean; positivity

theorem mean_le_weight_power {H s n : ℕ} (hH : 1 ≤ H) (hK : weight n ≤ 2 * s) :
    mean s n H ≤ (H : ℝ) ^ weight n := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  apply (div_le_iff₀ (pow_pos hH0 _)).mpr
  calc
    _ ≤ (H : ℝ) ^ (2 * s) := by exact_mod_cast momentCount_le_all_pairs H s n
    _ = _ := by rw [← pow_add]; congr 1; dsimp [exponent]; omega

/-- The prime and quotient powers cancel to the exact normalized cost. -/
theorem normalized_cost {H p q B : ℝ} {n d : ℕ}
    (hH : 0 ≤ H) (hp : 0 ≤ p) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hpB : p ^ n ≤ B ^ n * H) (hqp : q * p ≤ 2 * H) :
    H ^ n * p ^ (d + n ^ 2) * q ^ d ≤
      B ^ (n ^ 2) * 2 ^ d * H ^ (d + 2 * n) := by
  have hprime := pow_le_pow_left₀ (pow_nonneg hp n) hpB n
  have hprime' : p ^ (n ^ 2) ≤ B ^ (n ^ 2) * H ^ n := by
    simpa only [mul_pow, ← pow_mul, pow_two] using hprime
  have htail : q ^ d * p ^ d ≤ 2 ^ d * H ^ d := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hq hp) hqp d
  calc
    _ = p ^ (n ^ 2) * (q ^ d * p ^ d) * H ^ n := by rw [pow_add]; ring
    _ ≤ (B ^ (n ^ 2) * H ^ n) * (2 ^ d * H ^ d) * H ^ n := by gcongr
    _ = _ := by rw [pow_add, pow_mul, pow_two]; ring

/-- Normalize a concrete count bound once its power exponents have been identified. -/
theorem normalize_count_bound {H p q B A D J Jq : ℝ} {n d e : ℕ}
    (hH : 1 ≤ H) (hp : 0 ≤ p) (hq : 0 < q) (hB : 0 ≤ B)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hJq : 0 ≤ Jq) (he : e ≤ d + 2 * n)
    (hpB : p ^ n ≤ B ^ n * H) (hqp : q * p ≤ 2 * H)
    (hcount : J ≤ A * H ^ e + D * (H ^ n * p ^ (d + n ^ 2) * Jq)) :
    J / H ^ (d + 2 * n) ≤ A + D * B ^ (n ^ 2) * 2 ^ d * (Jq / q ^ d) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hz : 0 ≤ Jq / q ^ d := by positivity
  have hcost := normalized_cost (d := d) hH0.le hp hq.le hB hpB hqp
  apply (div_le_iff₀ (pow_pos hH0 _)).mpr
  calc
    _ ≤ _ := hcount
    _ ≤ A * H ^ (d + 2 * n) + D * (H ^ n * p ^ (d + n ^ 2) * Jq) := by gcongr
    _ = A * H ^ (d + 2 * n) + (D * (Jq / q ^ d)) *
        (H ^ n * p ^ (d + n ^ 2) * q ^ d) := by
      field_simp
    _ ≤ A * H ^ (d + 2 * n) + (D * (Jq / q ^ d)) *
        (B ^ (n ^ 2) * 2 ^ d * H ^ (d + 2 * n)) := by gcongr
    _ = _ := by ring

/-- A prime above the interval forces a degree-controlled trivial normalized bound. -/
theorem large_prime_weight_bound {H p B : ℝ} {n k : ℕ}
    (hH : 1 ≤ H) (hpH : H ≤ p) (_hB : 0 ≤ B) (hn : 1 ≤ n)
    (hk : k ≤ (n - 1) * (n + 1)) (hpB : p ^ n ≤ B ^ n * H) :
    H ^ k ≤ B ^ (n * (n + 1)) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hpow : H ^ (n - 1) ≤ B ^ n := by
    apply (mul_le_mul_iff_left₀ hH0).mp
    calc
      H ^ (n - 1) * H = H ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
      _ ≤ p ^ n := pow_le_pow_left₀ hH0.le hpH n
      _ ≤ _ := hpB
  calc
    _ ≤ H ^ ((n - 1) * (n + 1)) := pow_le_pow_right₀ hH hk
    _ = (H ^ (n - 1)) ^ (n + 1) := pow_mul _ _ _
    _ ≤ (B ^ n) ^ (n + 1) := pow_le_pow_left₀ (by positivity) hpow _
    _ = _ := (pow_mul _ _ _).symm

def primeFactor (C n : ℕ) : ℕ := 2 * C * (2 * n ^ 3 + 1) ^ 2 * n
def selectionCost (n s : ℕ) : ℕ := (n + s) ^ (2 * n) * (2 * n ^ 3 + 1) * n.factorial
def stepConstant (C n s : ℕ) : ℕ :=
  (2 * (n - 1) ^ (n + s) + 2 + selectionCost n s * 2 ^ (2 * s)) *
    primeFactor C n ^ (n * (n + 1))

theorem primeFactor_pos {C n : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) : 1 ≤ primeFactor C n := by
  unfold primeFactor
  have : 0 < C := by omega
  have : 0 < n := by omega
  change 0 < 2 * C * (2 * n ^ 3 + 1) ^ 2 * n
  positivity

theorem prime_power_le {C H n p : ℕ} (hH : 1 ≤ H) (hn : 1 ≤ n)
    (hp : p ≤ C * (2 * n ^ 3 + 1) ^ 2 * (n * rootCeil H n)) :
    (p : ℝ) ^ n ≤ (primeFactor C n : ℝ) ^ n * H := by
  have hroot := rootCeil_le_two_mul_root (n := n) hH
  have hp' : (p : ℝ) ≤ primeFactor C n * (H : ℝ) ^ ((n : ℝ)⁻¹) := by
    calc
      _ ≤ (C : ℝ) * (2 * (n : ℝ) ^ 3 + 1) ^ 2 * (n * rootCeil H n) := by
        exact_mod_cast hp
      _ ≤ (C : ℝ) * (2 * (n : ℝ) ^ 3 + 1) ^ 2 *
          (n * (2 * (H : ℝ) ^ ((n : ℝ)⁻¹))) := by gcongr
      _ = _ := by simp only [primeFactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]; ring
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg p) hp' n
  simpa only [mul_pow, Real.rpow_inv_natCast_pow (Nat.cast_nonneg H) (by omega : n ≠ 0)] using hpow

theorem quotient_mul_le {H p : ℕ} (hpH : p ≤ H) : (H / p + 1) * p ≤ 2 * H := by
  have := Nat.div_mul_le_self H p
  nlinarith

/-- The selected prime contracts the interval by the degree-dependent power. -/
theorem quotient_le_contract {H n p : ℕ} (hH : 1 ≤ H) (hn : 2 ≤ n)
    (hp : n * rootCeil H n < p) :
    ((H / p + 1 : ℕ) : ℝ) ≤ (H : ℝ) ^ (1 - (n : ℝ)⁻¹) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases hpH : p ≤ H
  · have hqp := quotient_mul_le hpH
    have h2 : 2 * rootCeil H n ≤ p :=
      (Nat.mul_le_mul_right (rootCeil H n) hn).trans hp.le
    have hqR : (H / p + 1) * rootCeil H n ≤ H := by
      have := Nat.mul_le_mul_left (H / p + 1) h2
      nlinarith
    have hr : (H : ℝ) ^ ((n : ℝ)⁻¹) ≤ (rootCeil H n : ℝ) := Nat.le_ceil _
    have hqr : ((H / p + 1 : ℕ) : ℝ) * (H : ℝ) ^ ((n : ℝ)⁻¹) ≤ H :=
      (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)).trans (by exact_mod_cast hqR)
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hH0 ((n : ℝ)⁻¹))).mp
    calc
      _ ≤ (H : ℝ) := hqr
      _ = _ := by rw [← Real.rpow_add hH0]; simp
  · rw [Nat.div_eq_of_lt (lt_of_not_ge hpH), zero_add, Nat.cast_one]
    apply Real.one_le_rpow (by exact_mod_cast hH)
    have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn0).mpr (by exact_mod_cast (show 1 ≤ n by omega))
    linarith

theorem stepConstant_bounds {C n : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) (s : ℕ) :
    2 * (n - 1) ^ (n + s) + 1 ≤ stepConstant C n s ∧
    selectionCost n s * primeFactor C n ^ (n ^ 2) * 2 ^ exponent s n ≤ stepConstant C n s ∧
    2 * primeFactor C n ^ (n * (n + 1)) ≤ stepConstant C n s := by
  have hB := primeFactor_pos hC hn
  have hBp : 1 ≤ primeFactor C n ^ (n * (n + 1)) := one_le_pow₀ hB
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 2 * (n - 1) ^ (n + s) + 2 + selectionCost n s * 2 ^ (2 * s) := by omega
      _ ≤ _ := le_mul_of_one_le_right (Nat.zero_le _) hBp
  · calc
      _ ≤ selectionCost n s * primeFactor C n ^ (n * (n + 1)) * 2 ^ (2 * s) := by
        gcongr
        · nlinarith
        · norm_num
        · exact Nat.sub_le _ _
      _ = (selectionCost n s * 2 ^ (2 * s)) * primeFactor C n ^ (n * (n + 1)) := by ring
      _ ≤ _ := by unfold stepConstant; gcongr; omega
  · unfold stepConstant
    gcongr
    omega

/-- The normalized recurrence with one absolute prime-supply constant and explicit step cost. -/
theorem normalized_recurrence :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ H n s : ℕ, 1 ≤ H → 2 ≤ n → n ^ 2 ≤ s →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (H : ℝ) ^ (1 - (n : ℝ)⁻¹) ∧
        mean (n + s) n H + 1 ≤ (stepConstant C n s : ℝ) * (mean s n q + 1) := by
  obtain ⟨C, hC, hrec⟩ := full_recurrence
  refine ⟨C, hC, ?_⟩
  intro H n s hH hn hs
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < s := by nlinarith
  obtain ⟨p, hp, hpL, hpU, _hshort, hcount⟩ := hrec H n s hH hn1 hs0
  let q : ℕ := H / p + 1
  have hq : 1 ≤ q := Nat.succ_le_succ (Nat.zero_le (H / p))
  refine ⟨q, hq, quotient_le_contract hH hn hpL, ?_⟩
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hB := primeFactor_pos hC hn1
  have hBreal : (1 : ℝ) ≤ primeFactor C n := by exact_mod_cast hB
  have hpB := prime_power_le hH hn1 hpU
  obtain ⟨he, hpe, hbad⟩ := exponent_identities hn1 hs
  obtain ⟨hA, hcoef, hlarge⟩ := stepConstant_bounds hC hn1 s
  have hAreal : (2 * (n - 1) ^ (n + s) : ℕ) + (1 : ℝ) ≤ stepConstant C n s := by
    exact_mod_cast hA
  have hcoefreal : (selectionCost n s : ℝ) * (primeFactor C n : ℝ) ^ (n ^ 2) *
      (2 : ℝ) ^ exponent s n ≤ stepConstant C n s := by exact_mod_cast hcoef
  have hlargeReal : 2 * (primeFactor C n : ℝ) ^ (n * (n + 1)) ≤ stepConstant C n s := by
    exact_mod_cast hlarge
  have hz := mean_nonneg s n q
  by_cases hpH : p ≤ H
  · have hcNat : momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n ≤
        (2 * (n - 1) ^ (n + s)) * H ^ (n + s + (n - 1)) +
          selectionCost n s * (H ^ n * p ^ (exponent s n + n ^ 2) *
            momentCount (Finset.Icc 1 (q : ℤ)) s n) := by
      convert hcount using 1
      rw [hpe]
      dsimp [selectionCost, q]
      ring
    have hcReal : (momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n : ℝ) ≤
        (2 * (n - 1) ^ (n + s) : ℕ) * (H : ℝ) ^ (n + s + (n - 1)) +
          (selectionCost n s : ℝ) * ((H : ℝ) ^ n * (p : ℝ) ^ (exponent s n + n ^ 2) *
            (momentCount (Finset.Icc 1 (q : ℤ)) s n : ℝ)) := by exact_mod_cast hcNat
    have hqpReal : (q : ℝ) * p ≤ 2 * H := by exact_mod_cast quotient_mul_le hpH
    have hnorm := normalize_count_bound (n := n) (d := exponent s n)
      hHreal (Nat.cast_nonneg p) hqreal (Nat.cast_nonneg (primeFactor C n))
      (Nat.cast_nonneg (2 * (n - 1) ^ (n + s))) (Nat.cast_nonneg (selectionCost n s))
      (Nat.cast_nonneg (momentCount (Finset.Icc 1 (q : ℤ)) s n))
      (by omega : n + s + (n - 1) ≤ exponent s n + 2 * n) hpB hqpReal hcReal
    have hnorm' : mean (n + s) n H ≤ (2 * (n - 1) ^ (n + s) : ℕ) +
        (selectionCost n s : ℝ) * (primeFactor C n : ℝ) ^ (n ^ 2) *
          (2 : ℝ) ^ exponent s n * mean s n q := by
      simpa only [mean, he] using hnorm
    have hmul := mul_le_mul_of_nonneg_right hcoefreal hz
    nlinarith
  · have hw : weight n ≤ 2 * (n + s) := by
      have := (weight_le_sq hn1).trans hs
      omega
    have hlargeBound := large_prime_weight_bound hHreal
      (show (H : ℝ) ≤ p by exact_mod_cast (lt_of_not_ge hpH).le)
      (Nat.cast_nonneg (primeFactor C n)) hn1 (weight_le_pred_mul hn) hpB
    have hnorm := (mean_le_weight_power hH hw).trans hlargeBound
    have hBp : (1 : ℝ) ≤ (primeFactor C n : ℝ) ^ (n * (n + 1)) := one_le_pow₀ hBreal
    calc
      _ ≤ 2 * (primeFactor C n : ℝ) ^ (n * (n + 1)) := by linarith
      _ ≤ _ := hlargeReal
      _ ≤ _ := le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)

end NField.Alignment.VinogradovNormalizedRecurrence
