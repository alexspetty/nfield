/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothDivisor

/-!
# Rankin's bound for the actual smooth-integer count

The smooth predicate includes one and excludes zero. Both cutoffs are real,
and their endpoints are included. The power sum is over a finite set of
allowed primes, so convergence holds for every positive exponent.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothCount

open scoped BigOperators
open HarperSmoothDivisor CollisionMertensInput

def smoothSet (x y : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊x⌋₊).filter (· ∈ smoothIntegers y)
def smoothCount (x y : ℝ) : ℝ := (smoothSet x y).card
def shiftedProduct (y sigma : ℝ) : ℝ := ∏ p ∈ primesUpTo y, (1 - (p : ℝ)^(-sigma))⁻¹

theorem smoothSet_mem {x y : ℝ} {n : ℕ} : n ∈ smoothSet x y ↔
    0 < n ∧ (n : ℝ) ≤ x ∧ n ∈ smoothIntegers y := by
  simp only [smoothSet, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hn, hnx⟩, hy⟩
    exact ⟨hn, (Nat.le_floor_iff' hn.ne').mp hnx, hy⟩
  · rintro ⟨hn, hnx, hy⟩
    exact ⟨⟨hn, (Nat.le_floor_iff' hn.ne').mpr hnx⟩, hy⟩

theorem one_mem_smoothSet {x y : ℝ} (hx : 1 ≤ x) : 1 ∈ smoothSet x y := by
  rw [smoothSet_mem, smoothIntegers_mem]
  refine ⟨by norm_num, by simpa using hx, by norm_num, ?_⟩
  intro p hp hp1
  exact False.elim (hp.not_dvd_one hp1)

def powerHom (sigma : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-sigma)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem smooth_power_hasSum (y : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    HasSum (fun n : smoothIntegers y => ((n : ℕ) : ℝ)^(-sigma)) (shiftedProduct y sigma) := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖powerHom sigma p‖ < 1 := by
    change ‖(p : ℝ)^(-sigma)‖ < 1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerHom sigma) (fun {_} hp => hprime hp) (primesUpTo y)).2
  have hf : (primesUpTo y).filter Nat.Prime = primesUpTo y :=
    Finset.filter_true_of_mem (fun _ hp => (primesUpTo_mem.mp hp).1)
  simpa only [hf, powerHom, MonoidHom.coe_mk, OneHom.coe_mk, shiftedProduct, smoothIntegers] using h

theorem smooth_partial_power_bound (y : ℝ) {sigma : ℝ} (hs : 0 < sigma) (s : Finset ℕ) :
    (∑ n ∈ s.filter (· ∈ smoothIntegers y), (n : ℝ)^(-sigma)) ≤ shiftedProduct y sigma := by
  have h := smooth_power_hasSum y hs
  have hsum : Summable ((smoothIntegers y).indicator (fun n : ℕ => (n : ℝ)^(-sigma))) :=
    (summable_subtype_iff_indicator (s := smoothIntegers y)
      (f := fun n : ℕ => (n : ℝ)^(-sigma))).mp h.summable
  have he : (∑' n : ℕ, (smoothIntegers y).indicator (fun n : ℕ => (n : ℝ)^(-sigma)) n) =
      shiftedProduct y sigma :=
    (tsum_subtype (smoothIntegers y) (fun n : ℕ => (n : ℝ)^(-sigma))).symm.trans h.tsum_eq
  rw [← he]
  simpa only [Finset.sum_filter, Set.indicator_apply] using
    hsum.sum_le_tsum s (fun n _ => by simp only [Set.indicator_apply]; split_ifs <;> positivity)

theorem rankin_bound {x : ℝ} (hx : 0 < x) (y : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    smoothCount x y ≤ x^sigma * shiftedProduct y sigma := by
  calc
    _ = ∑ _n ∈ smoothSet x y, (1 : ℝ) := by simp [smoothCount]
    _ ≤ ∑ n ∈ smoothSet x y, x^sigma * (n : ℝ)^(-sigma) := by
      apply Finset.sum_le_sum
      intro n hn
      have hmem := smoothSet_mem.mp hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hmem.1
      calc
        (1 : ℝ) = (n : ℝ)^sigma * (n : ℝ)^(-sigma) := by
          rw [← Real.rpow_add hnR]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hnR.le hmem.2.1 hs.le) (by positivity)
    _ = x^sigma * ∑ n ∈ smoothSet x y, (n : ℝ)^(-sigma) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (smooth_partial_power_bound y hs _) (by positivity)

end NField.Alignment.HarperSmoothCount
