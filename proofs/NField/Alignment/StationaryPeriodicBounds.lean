/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryDiagonalDefinitions
import NField.Alignment.CollisionCycleStationarity
import NField.Alignment.CollisionRemainderCovariance

/-! # Uniform incomplete-cycle errors for the actual integer remainders -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryPeriodicBounds
open scoped BigOperators
open CollisionRemainderDynamics CollisionCycleStationarity CollisionRemainderCovariance

theorem sum_Ioc_eq_prefix_difference (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, f n) =
      (∑ n ∈ Finset.range (b + 1), f n) - ∑ n ∈ Finset.range (a + 1), f n := by
  have he : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by ext n; simp
  rw [he, Finset.sum_Ico_eq_sub _ (by omega)]

theorem periodic_prefix_bound {f : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : Function.Periodic f k) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |f n| ≤ B)
    (hz : (∑ n ∈ Finset.range k, f n) = 0) (N : ℕ) :
    |∑ n ∈ Finset.range N, f n| ≤ (k : ℝ) * B := by
  rw [periodic_sum_decomposition f k N hf, hz, mul_zero, zero_add]
  calc
    _ ≤ ∑ n ∈ Finset.range (N % k), |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (N % k), B := Finset.sum_le_sum (fun _ _ => hb _)
    _ = (N % k : ℕ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt N hk).le) hB

theorem periodic_interval_bound {f : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : Function.Periodic f k) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |f n| ≤ B)
    (hz : (∑ n ∈ Finset.range k, f n) = 0) {a b : ℕ} (hab : a ≤ b) :
    |∑ n ∈ Finset.Ioc a b, f n| ≤ 2 * (k : ℝ) * B := by
  rw [sum_Ioc_eq_prefix_difference f hab]
  calc
    _ ≤ |∑ n ∈ Finset.range (b + 1), f n| + |∑ n ∈ Finset.range (a + 1), f n| := abs_sub _ _
    _ ≤ (k : ℝ) * B + (k : ℝ) * B :=
      add_le_add (periodic_prefix_bound hk hf hB hb hz _) (periodic_prefix_bound hk hf hB hb hz _)
    _ = _ := by ring

theorem periodic_centered_interval_bound {f : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : Function.Periodic f k) {B c : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |f n| ≤ B)
    (hc : (∑ n ∈ Finset.range k, f n) = (k : ℝ) * c) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, f n) - ((b : ℝ) - a) * c| ≤ 4 * (k : ℝ) * B := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcb : |c| ≤ B := by
    have hh : |(k : ℝ) * c| ≤ (k : ℝ) * B := by
      rw [← hc]
      calc
        _ ≤ ∑ n ∈ Finset.range k, |f n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.range k, B := Finset.sum_le_sum (fun _ _ => hb _)
        _ = _ := by simp
    rw [abs_mul, abs_of_pos hkR] at hh
    exact (mul_le_mul_iff_right₀ hkR).mp hh
  have hzero : (∑ n ∈ Finset.range k, (f n - c)) = 0 := by
    rw [Finset.sum_sub_distrib, hc]
    simp
  have hbound (n : ℕ) : |f n - c| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by linarith [hb n])
  have hcp : Function.Periodic (fun _ : ℕ => c) k := fun _ => rfl
  have hh := periodic_interval_bound hk (hf.sub hcp)
    (by positivity : 0 ≤ 2 * B) hbound hzero hab
  have hcard : ((Finset.Ioc a b).card : ℝ) = (b : ℝ) - a := by
    rw [Nat.card_Ioc, Nat.cast_sub hab]
  simpa only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
    show 2 * (k : ℝ) * (2 * B) = 4 * (k : ℝ) * B by ring] using hh

theorem centered_remainder_periodic (k : ℕ) : Function.Periodic (centeredRemainder k) k := by
  intro n
  simp [centeredRemainder, Nat.add_mod_right]

theorem centered_remainder_abs {k : ℕ} (hk : 0 < k) (n : ℕ) :
    |centeredRemainder k n| ≤ (k : ℝ) / 2 := by
  have hm : ((n % k : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast Nat.mod_lt n hk
  have hn : (0 : ℝ) ≤ (n % k : ℕ) := by positivity
  unfold centeredRemainder
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Title: `An incomplete centered-residue interval has a quadratic period bound`. -/
theorem centered_remainder_interval_bound {k : ℕ} (hk : 0 < k) {a b : ℕ} (hab : a ≤ b) :
    |∑ n ∈ Finset.Ioc a b, centeredRemainder k n| ≤ (k : ℝ) ^ 2 := by
  have hh := periodic_interval_bound hk (centered_remainder_periodic k)
    (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2) (centered_remainder_abs hk)
    (centered_cycle_sum hk) hab
  convert hh using 1 <;> ring

theorem centered_product_periodic (k l : ℕ) :
    Function.Periodic (fun n => centeredRemainder k n * centeredRemainder l n) (k.lcm l) := by
  have hk := (centered_remainder_periodic k).nat_mul (k.lcm l / k)
  have hl := (centered_remainder_periodic l).nat_mul (k.lcm l / l)
  simp only [Nat.cast_id, Nat.div_mul_cancel (Nat.dvd_lcm_left k l)] at hk
  simp only [Nat.cast_id, Nat.div_mul_cancel (Nat.dvd_lcm_right k l)] at hl
  exact hk.mul hl

/-- Title: `Finite-interval residue covariance has the product-period error`. -/
theorem centered_product_interval_bound {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, centeredRemainder k n * centeredRemainder l n) -
      ((b : ℝ) - a) * (((k.gcd l : ℝ) ^ 2 - 1) / 12)| ≤ (k : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
  have hb (n : ℕ) : |centeredRemainder k n * centeredRemainder l n| ≤ (k : ℝ) * l / 4 := by
    rw [abs_mul]
    calc
      _ ≤ ((k : ℝ) / 2) * ((l : ℝ) / 2) :=
        mul_le_mul (centered_remainder_abs hk n) (centered_remainder_abs hl n) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hc : (∑ n ∈ Finset.range (k.lcm l), centeredRemainder k n * centeredRemainder l n) =
      (k.lcm l : ℝ) * (((k.gcd l : ℝ) ^ 2 - 1) / 12) := by
    rw [remainder_covariance_sum hk hl]
    ring
  have hh := periodic_centered_interval_bound (Nat.lcm_pos hk hl) (centered_product_periodic k l)
    (by positivity : (0 : ℝ) ≤ (k : ℝ) * l / 4) hb hc hab
  have hL : (k.lcm l : ℝ) ≤ (k : ℝ) * l := by exact_mod_cast Nat.lcm_le_mul hk hl
  calc
    _ ≤ 4 * (k.lcm l : ℝ) * ((k : ℝ) * l / 4) := hh
    _ ≤ 4 * ((k : ℝ) * l) * ((k : ℝ) * l / 4) := by gcongr
    _ = _ := by ring

end NField.Alignment.StationaryPeriodicBounds
