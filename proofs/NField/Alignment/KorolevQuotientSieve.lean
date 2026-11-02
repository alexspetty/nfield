/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevFirstExclusion

/-!
# Rough-number bounds uniform in the smaller quotient

The fixed Q^4 Selberg error cannot be summed unchanged over smooth
factors. Sieve instead at min(Q,t^(1/8)), so its error is at most sqrt(t).
This gives a rough-count bound uniform for all t >= Q once Q is large.
Excluding the integer one then permits all smaller nonnegative quotients,
including t < Q where the counted set is empty.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevQuotientSieve
open scoped BigOperators Topology
open Filter KorolevFirstExclusion HarperSieveBound HarperIntervalSieve

def nontrivialRoughSet (t Q : ℝ) : Finset ℕ := (roughSet t Q).filter (fun n => 1 < n)

theorem roughSet_antitone {t P Q : ℝ} (ht : 0 ≤ t) (hPQ : P ≤ Q) :
    roughSet t Q ⊆ roughSet t P := by
  intro n hn
  obtain ⟨hn0, hnt, hp⟩ := (roughSet_mem ht n).mp hn
  exact (roughSet_mem ht n).mpr ⟨hn0, hnt, fun p hpp hpn => hPQ.trans_lt (hp p hpp hpn)⟩

theorem nontrivialRoughSet_empty {t Q : ℝ} (ht : 0 ≤ t) (htQ : t ≤ Q) :
    nontrivialRoughSet t Q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hn, hn1⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn0, hnt, hp⟩ := (roughSet_mem ht n).mp hn
  obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hple : (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn0 hpn
  exact (not_le_of_gt (hp p hpp hpn)) (hple.trans (hnt.trans htQ))

/-- Explicit bound once the elementary logarithm/square-root comparison
holds. The sieve truncation depends on the actual quotient t. -/
theorem rough_count_bound {t Q : ℝ} (hQ : 256 ≤ Q) (hQt : Q ≤ t)
    (hlog : Real.log t ≤ Real.sqrt t) :
    ((roughSet t Q).card : ℝ) ≤ 17 * (t * Real.log t / (Real.log Q)^2) := by
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlQt : Real.log Q ≤ Real.log t := Real.log_le_log hQ0 hQt
  let R : ℝ := t ^ (1 / 8 : ℝ)
  have hR : 2 ≤ R := by
    have hh : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
      norm_num [show (256 : ℝ) = 2^8 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← hh]
    exact Real.rpow_le_rpow (by norm_num) (hQ.trans hQt) (by norm_num)
  have hRlog : Real.log R = Real.log t / 8 := by
    dsimp only [R]
    rw [Real.log_rpow ht0]
    ring
  have hRfour : R^4 = Real.sqrt t := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast ht0.le, Real.sqrt_eq_rpow]
    norm_num
  have hscale : t / Real.log t ≤ t * Real.log t / (Real.log Q)^2 := by
    apply (div_le_div_iff₀ hlt (sq_pos_of_pos hlQ)).mpr
    have hs : (Real.log Q)^2 ≤ (Real.log t)^2 := pow_le_pow_left₀ hlQ.le hlQt 2
    nlinarith [mul_le_mul_of_nonneg_left hs ht0.le]
  have hsqrt : Real.sqrt t ≤ t / Real.log t := by
    apply (le_div_iff₀ hlt).mpr
    calc
      Real.sqrt t * Real.log t ≤ Real.sqrt t * Real.sqrt t :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
      _ = t := Real.mul_self_sqrt ht0.le
  have hnonneg : 0 ≤ t * Real.log t / (Real.log Q)^2 := by positivity
  by_cases hQR : Q ≤ R
  · have hb := rough_interval_bound (a := 0) (b := t) (P := Q)
      (by norm_num) ht0.le (by linarith)
    change ((roughSet t Q).card : ℝ) ≤ 2 * (t - 0) / Real.log Q + Q^4 at hb
    have herr : Q^4 ≤ Real.sqrt t := by
      rw [← hRfour]
      exact pow_le_pow_left₀ hQ0.le hQR 4
    have hmain : t / Real.log Q ≤ t * Real.log t / (Real.log Q)^2 := by
      apply (div_le_div_iff₀ hlQ (sq_pos_of_pos hlQ)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlQt (mul_nonneg ht0.le hlQ.le)]
    have h := hsqrt.trans hscale
    nlinarith [show 2 * (t - 0) / Real.log Q = 2 * (t / Real.log Q) by ring]
  · have hRQ : R ≤ Q := (lt_of_not_ge hQR).le
    have hb := rough_interval_bound (a := 0) (b := t) (P := R)
      (by norm_num) ht0.le hR
    change ((roughSet t R).card : ℝ) ≤ 2 * (t - 0) / Real.log R + R^4 at hb
    rw [hRlog, hRfour] at hb
    have hcard : ((roughSet t Q).card : ℝ) ≤ ((roughSet t R).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (roughSet_antitone ht0.le hRQ)
    have h := hsqrt.trans hscale
    have he : 2 * (t - 0) / (Real.log t / 8) = 16 * (t / Real.log t) := by ring
    rw [he] at hb
    linarith

theorem eventual_uniform_rough_count : ∀ᶠ Q : ℝ in atTop, ∀ t : ℝ, Q ≤ t →
    ((roughSet t Q).card : ℝ) ≤ 17 * (t * Real.log t / (Real.log Q)^2) := by
  have he : ∀ᶠ t : ℝ in atTop, Real.log t ≤ Real.sqrt t := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    simpa only [Real.norm_of_nonneg (Real.log_nonneg ht1),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t) _), one_mul,
      Real.sqrt_eq_rpow] using ht
  obtain ⟨T, hT⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop (max T 256)] with Q hQ t hQt
  exact rough_count_bound ((le_max_right T 256).trans hQ) hQt
    (hT t ((le_max_left T 256).trans (hQ.trans hQt)))

/-- Uniform in every smaller quotient t. The excluded term n=1 is
essential when t is below Q. No error per smooth factor remains. -/
theorem eventual_quotient_bound : ∀ᶠ Q : ℝ in atTop, ∀ x t : ℝ,
    Q ≤ x → 0 ≤ t → t ≤ x →
      ((nontrivialRoughSet t Q).card : ℝ) ≤ 17 * (t * Real.log x / (Real.log Q)^2) := by
  filter_upwards [eventual_uniform_rough_count, eventually_ge_atTop (2 : ℝ)]
    with Q hQ hQ2 x t hQx ht htx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  by_cases htQ : t ≤ Q
  · rw [nontrivialRoughSet_empty ht htQ, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hQt : Q ≤ t := (lt_of_not_ge htQ).le
    have hcard : ((nontrivialRoughSet t Q).card : ℝ) ≤ ((roughSet t Q).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (roughSet t Q) (fun n : ℕ => 1 < n)
    apply hcard.trans ((hQ t hQt).trans _)
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) htx) ht)
        (sq_nonneg _)) (by norm_num)

/-- The finite smooth-factor sum used in the source decomposition. No
uncontrolled sieve remainder is multiplied by the number of factors. -/
theorem eventual_factor_sum_bound : ∀ᶠ Q : ℝ in atTop, ∀ x : ℝ, Q ≤ x →
    ∀ l : ℕ, 0 < l → ∀ W : Finset ℕ, (∀ w ∈ W, 0 < w) →
      (∑ w ∈ W, ((nontrivialRoughSet (x / ((l : ℝ)^2 * w)) Q).card : ℝ)) ≤
        (17 * x * Real.log x / ((l : ℝ)^2 * (Real.log Q)^2)) *
          ∑ w ∈ W, (1 : ℝ) / w := by
  filter_upwards [eventual_quotient_bound, eventually_ge_atTop (2 : ℝ)]
    with Q hQ hQ2 x hQx l hl W hW
  have hx : 0 ≤ x := by linarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hlog : Real.log Q ≠ 0 := (Real.log_pos (by linarith : 1 < Q)).ne'
  calc
    _ ≤ ∑ w ∈ W, (17 * x * Real.log x / ((l : ℝ)^2 * (Real.log Q)^2)) *
        ((1 : ℝ) / w) := by
      apply Finset.sum_le_sum
      intro w hw
      have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hW w hw
      have hw0 : (w : ℝ) ≠ 0 := by positivity
      have hd : (1 : ℝ) ≤ (l : ℝ)^2 * w := by nlinarith
      have ht : x / ((l : ℝ)^2 * w) ≤ x :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < (l : ℝ)^2 * w)).mpr (by nlinarith)
      have hb := hQ x (x / ((l : ℝ)^2 * w)) hQx (by positivity) ht
      calc
        _ ≤ 17 * ((x / ((l : ℝ)^2 * w)) * Real.log x / (Real.log Q)^2) := hb
        _ = _ := by field_simp [hl0, hw0, hlog]
    _ = _ := by rw [Finset.mul_sum]

end NField.Alignment.KorolevQuotientSieve
