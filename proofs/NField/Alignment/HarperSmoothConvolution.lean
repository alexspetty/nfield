/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothDivisor
import NField.Alignment.HarperMomentExpansion
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Smooth divisors and the weighted convolution estimate

The smooth-divisor count is the literal count used in the manuscript.
Submultiplicativity follows by splitting every divisor of a product into
two divisors. Cauchy--Schwarz is then applied separately at each complete
integer index. No moment estimate is taken as a hypothesis.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothConvolution

open scoped BigOperators
open HarperSmoothDivisor HarperMomentExpansion

theorem smooth_of_dvd {P : ℝ} {d n : ℕ} (hn : n ∈ smoothIntegers P) (hd : d ∣ n) :
    d ∈ smoothIntegers P := by
  obtain ⟨hn0, hn⟩ := smoothIntegers_mem.mp hn
  exact smoothIntegers_mem.mpr ⟨ne_zero_of_dvd_ne_zero hn0 hd,
    fun p hp hpd => hn p hp (hpd.trans hd)⟩

theorem smooth_mul {P : ℝ} {n m : ℕ}
    (hn : n ∈ smoothIntegers P) (hm : m ∈ smoothIntegers P) :
    n * m ∈ smoothIntegers P := by
  obtain ⟨hn0, hn⟩ := smoothIntegers_mem.mp hn
  obtain ⟨hm0, hm⟩ := smoothIntegers_mem.mp hm
  refine smoothIntegers_mem.mpr ⟨mul_ne_zero hn0 hm0, fun p hp hpm => ?_⟩
  exact (hp.dvd_mul.mp hpm).elim (hn p hp) (hm p hp)

theorem smooth_one (P : ℝ) : 1 ∈ smoothIntegers P := by
  rw [smoothIntegers_mem]
  exact ⟨one_ne_zero, fun p hp h => False.elim (hp.not_dvd_one h)⟩

theorem smooth_prod {ι : Type*} {P : ℝ} (s : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ s, a i ∈ smoothIntegers P) : (∏ i ∈ s, a i) ∈ smoothIntegers P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smooth_one P
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact smooth_mul (ha i (Finset.mem_insert_self ..))
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- This holds for arbitrary factors, including zero. -/
theorem smoothDivisorCount_mul_le (P : ℝ) (n m : ℕ) :
    smoothDivisorCount P (n * m) ≤ smoothDivisorCount P n * smoothDivisorCount P m := by
  classical
  by_cases hn : n = 0
  · simp [hn, smoothDivisorCount]
  by_cases hm : m = 0
  · simp [hm, smoothDivisorCount]
  let D (u : ℕ) := u.divisors.filter (· ∈ smoothIntegers P)
  have hsub : D (n * m) ⊆ (D n ×ˢ D m).image (fun t => t.1 * t.2) := by
    intro d hd
    obtain ⟨hddiv, hds⟩ := Finset.mem_filter.mp hd
    obtain ⟨u, v, hun, hvm, huv⟩ :=
      exists_dvd_and_dvd_of_dvd_mul (Nat.mem_divisors.mp hddiv).1
    apply Finset.mem_image.mpr
    refine ⟨(u, v), Finset.mem_product.mpr ⟨?_, ?_⟩, huv.symm⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hun, hn⟩,
        smooth_of_dvd hds (huv ▸ dvd_mul_right u v)⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hvm, hm⟩,
        smooth_of_dvd hds (huv ▸ dvd_mul_left v u)⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq (Finset.card_product ..))

theorem smoothDivisorCount_prod_le {ι : Type*} (P : ℝ) (s : Finset ι) (a : ι → ℕ) :
    smoothDivisorCount P (∏ i ∈ s, a i) ≤ ∏ i ∈ s, smoothDivisorCount P (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (smoothDivisorCount_mul_le P _ _).trans (Nat.mul_le_mul_left _ ih)

theorem smoothDivisorCount_eq_card {P : ℝ} {n : ℕ} (hn : n ∈ smoothIntegers P) :
    smoothDivisorCount P n = n.divisors.card := by
  unfold smoothDivisorCount
  rw [Finset.filter_true_of_mem (fun d hd => smooth_of_dvd hn (Nat.mem_divisors.mp hd).1)]

theorem prime_smooth {P : ℝ} {p : ℕ} (hp : p.Prime) (hP : (p : ℝ) ≤ P) :
    p ∈ smoothIntegers P := by
  refine smoothIntegers_mem.mpr ⟨hp.ne_zero, fun q hq hqp => ?_⟩
  obtain rfl | rfl := (Nat.dvd_prime hp).mp hqp
  · exact False.elim (Nat.not_prime_one hq)
  · exact hP

theorem smooth_pow {P : ℝ} {n : ℕ} (hn : n ∈ smoothIntegers P) (k : ℕ) :
    n ^ k ∈ smoothIntegers P := by
  induction k with
  | zero => simpa using smooth_one P
  | succ k ih => simpa only [pow_succ] using smooth_mul ih hn

/-- In particular, the prime and prime-square divisor weights are exactly two and three. -/
theorem smoothDivisorCount_prime_pow {P : ℝ} {p : ℕ} (hp : p.Prime)
    (hP : (p : ℝ) ≤ P) (k : ℕ) : smoothDivisorCount P (p ^ k) = k + 1 := by
  rw [smoothDivisorCount_eq_card (smooth_pow (prime_smooth hp hP) k),
    Nat.divisors_prime_pow hp]
  simp

/-- Cauchy--Schwarz in the form needed for each coefficient fiber. -/
theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (b : ι → ℂ) :
    ‖∑ i ∈ s, b i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖b i‖) ^ 2 := by
      gcongr
      exact norm_sum_le s b
    _ ≤ _ := by simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖b i‖)

def convolutionCoefficient (s t : Finset ℕ) (c b : ℕ → ℂ) (u : ℕ) : ℂ :=
  groupedCoefficient (s ×ˢ t) (fun v => v.1 * v.2) (fun v => c v.1 * b v.2) u

theorem product_fiber_card_le {P : ℝ} (s t : Finset ℕ) (u : ℕ) (hu : u ≠ 0)
    (ht : ∀ m ∈ t, m ∈ smoothIntegers P) :
    ((s ×ˢ t).filter (fun v => v.1 * v.2 = u)).card ≤ smoothDivisorCount P u := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro v hv
    obtain ⟨hv, he⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨he ▸ dvd_mul_left v.2 v.1, hu⟩, ht v.2 (Finset.mem_product.mp hv).2⟩
  · intro v hv w hw he
    apply Prod.ext _ he
    have hvp := (Finset.mem_filter.mp hv).2
    have hwp := (Finset.mem_filter.mp hw).2
    have hv0 : v.2 ≠ 0 := (smoothIntegers_mem.mp
      (ht v.2 (Finset.mem_product.mp (Finset.mem_filter.mp hv).1).2)).1
    exact (mul_right_cancel₀ hv0) (by simpa only [← he] using hvp.trans hwp.symm)

theorem convolution_coefficient_bound {P : ℝ} (s t : Finset ℕ) (c b : ℕ → ℂ)
    (u : ℕ) (hu : u ≠ 0) (ht : ∀ m ∈ t, m ∈ smoothIntegers P) :
    ‖convolutionCoefficient s t c b u‖ ^ 2 ≤
      ∑ v ∈ (s ×ˢ t).filter (fun v => v.1 * v.2 = u),
        ((smoothDivisorCount P v.1 : ℝ) * ‖c v.1‖ ^ 2) *
          ((smoothDivisorCount P v.2 : ℝ) * ‖b v.2‖ ^ 2) := by
  classical
  let F := (s ×ˢ t).filter (fun v => v.1 * v.2 = u)
  calc
    _ ≤ (F.card : ℝ) * ∑ v ∈ F, ‖c v.1 * b v.2‖ ^ 2 := norm_sum_sq_le _ _
    _ ≤ (smoothDivisorCount P u : ℝ) * ∑ v ∈ F, ‖c v.1 * b v.2‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast product_fiber_card_le s t u hu ht)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = ∑ v ∈ F, (smoothDivisorCount P u : ℝ) * ‖c v.1 * b v.2‖ ^ 2 :=
      Finset.mul_sum ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      have hd : (smoothDivisorCount P u : ℝ) ≤
          (smoothDivisorCount P v.1 : ℝ) * (smoothDivisorCount P v.2 : ℝ) := by
        rw [← (Finset.mem_filter.mp hv).2]
        exact_mod_cast smoothDivisorCount_mul_le P v.1 v.2
      calc
        _ ≤ ((smoothDivisorCount P v.1 : ℝ) * (smoothDivisorCount P v.2 : ℝ)) *
            ‖c v.1 * b v.2‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
        _ = _ := by rw [norm_mul]; ring

/-- The smooth weighted convolution bound, with constant one. -/
theorem convolution_energy_bound {P : ℝ} (s t : Finset ℕ) (c b : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≠ 0) (ht : ∀ m ∈ t, m ∈ smoothIntegers P) :
    (∑ u ∈ (s ×ˢ t).image (fun v => v.1 * v.2), ‖convolutionCoefficient s t c b u‖ ^ 2) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖c n‖ ^ 2) *
        (∑ m ∈ t, (smoothDivisorCount P m : ℝ) * ‖b m‖ ^ 2) := by
  classical
  calc
    _ ≤ ∑ u ∈ (s ×ˢ t).image (fun v => v.1 * v.2),
        ∑ v ∈ (s ×ˢ t).filter (fun v => v.1 * v.2 = u),
          ((smoothDivisorCount P v.1 : ℝ) * ‖c v.1‖ ^ 2) *
            ((smoothDivisorCount P v.2 : ℝ) * ‖b v.2‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hn, hm⟩ := Finset.mem_product.mp hv
      exact convolution_coefficient_bound s t c b _
        (mul_ne_zero (hs v.1 hn) (smoothIntegers_mem.mp (ht v.2 hm)).1) ht
    _ = ∑ v ∈ s ×ˢ t,
        ((smoothDivisorCount P v.1 : ℝ) * ‖c v.1‖ ^ 2) *
          ((smoothDivisorCount P v.2 : ℝ) * ‖b v.2‖ ^ 2) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem _ hv) _
    _ = _ := by rw [Finset.sum_product]; simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

end NField.Alignment.HarperSmoothConvolution
