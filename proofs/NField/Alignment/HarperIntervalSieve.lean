/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

/-
# Actual interval model for the rough-number sieve

The prime base is squarefree, reciprocal density is multiplicative, and
every positive divisor has interval-counting remainder at most one.
-/

import NField.Alignment.HarperSmoothRough
import Mathlib.NumberTheory.SelbergSieve

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperIntervalSieve

open scoped BigOperators
open HarperSmoothRough CollisionMertensInput

theorem primeBase_squarefree (P : ℝ) : Squarefree (primeBase P) := by
  unfold primeBase
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun r hr s hs hrs => ?_)
    (fun r hr => (primesUpTo_mem.mp hr).1.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (primesUpTo_mem.mp hr).1 (primesUpTo_mem.mp hs).1).mpr hrs

def reciprocalDensity : ArithmeticFunction ℝ := ⟨fun d => (d : ℝ)⁻¹, by simp⟩

theorem reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  constructor
  · simp [reciprocalDensity]
  · intro m n _
    simp [reciprocalDensity, Nat.cast_mul, mul_comm]

def intervalSupport (a b : ℝ) : Finset ℕ := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊

theorem intervalSupport_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    n ∈ intervalSupport a b ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp only [intervalSupport, Finset.mem_Ioc, Nat.floor_lt ha, Nat.le_floor_iff (ha.trans hab)]

theorem interval_multiple_card {a b : ℕ} (hab : a ≤ b) (d : ℕ) :
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card = b/d-a/d := by
  have he : (Finset.Ioc a b).filter (fun n => d ∣ n) =
      ((Finset.Ioc 0 b).filter (fun n => d ∣ n)) \
        ((Finset.Ioc 0 a).filter (fun n => d ∣ n)) := by
    ext n
    by_cases hd : d ∣ n
    · simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc, hd, and_true]
      omega
    · simp [hd]
  rw [he, Finset.card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, hd⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
    ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hab⟩, hd⟩

theorem interval_multiple_error {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {d : ℕ} (hd : 0 < d) :
    |(((intervalSupport a b).filter (fun n => d ∣ n)).card : ℝ) - (b-a)/(d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haD : 0 ≤ a/(d : ℝ) := div_nonneg ha hdR.le
  have hbD : 0 ≤ b/(d : ℝ) := div_nonneg (ha.trans hab) hdR.le
  have habD : a/(d : ℝ) ≤ b/(d : ℝ) := div_le_div_of_nonneg_right hab hdR.le
  rw [intervalSupport, interval_multiple_card (Nat.floor_mono hab),
    ← Nat.floor_div_natCast, ← Nat.floor_div_natCast,
    Nat.cast_sub (Nat.floor_mono habD), sub_div]
  apply abs_le.mpr
  constructor <;> linarith [Nat.floor_le haD, Nat.floor_le hbD,
    Nat.lt_floor_add_one (a/(d : ℝ)), Nat.lt_floor_add_one (b/(d : ℝ))]

def roughIntervalSieve (a b P : ℝ) : BoundingSieve where
  support := intervalSupport a b
  prodPrimes := primeBase P
  prodPrimes_squarefree := primeBase_squarefree P
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := b-a
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := fun p hp _ => by
    change 0 < (p : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => by
    change (p : ℝ)⁻¹ < 1
    rw [inv_eq_one_div]
    exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

theorem roughIntervalSieve_siftedSum (a b P : ℝ) :
    (roughIntervalSieve a b P).siftedSum =
      (((intervalSupport a b).filter (fun n => n.Coprime (primeBase P))).card : ℝ) := by
  simp [BoundingSieve.siftedSum, roughIntervalSieve, Nat.coprime_comm]

theorem roughIntervalSieve_remainder {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (P : ℝ) {d : ℕ} (hd : 0 < d) : |(roughIntervalSieve a b P).rem d| ≤ 1 := by
  have h := interval_multiple_error ha hab hd
  simpa [BoundingSieve.rem, BoundingSieve.multSum, roughIntervalSieve,
    reciprocalDensity, div_eq_mul_inv, mul_comm] using h

end NField.Alignment.HarperIntervalSieve
