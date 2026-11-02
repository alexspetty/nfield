/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothDivisor
import NField.Alignment.SupportedPrimeExponentCone
import NField.Alignment.SupportedRoughDecomposition
import NField.Alignment.HarperActualConditioning
import Mathlib.Algebra.BigOperators.Associated

/-!
# Canonical smooth and rough factors at a real prime cutoff

Connect the existing supported/rough factorization with the literal positive
smooth-integer predicate. The actual Harper partition, including prime-square
terms, depends only on Haar coordinates at primes at most the cutoff.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothRough

open scoped BigOperators
open HarperSmoothDivisor CollisionMertensInput SupportedPrimeExponentCone
  SteinhausMoment HarperActualConditioning HarperRoundedCutoff HarperPrimeTaylorComparison

def primeBase (P : ℝ) : ℕ := ∏ r ∈ primesUpTo P, r

theorem primeBase_pos (P : ℝ) : 0 < primeBase P :=
  Finset.prod_pos (fun _ hr => (primesUpTo_mem.mp hr).1.pos)

theorem prime_dvd_primeBase {P : ℝ} {r : ℕ} (hr : r.Prime) :
    r ∣ primeBase P ↔ r ∈ primesUpTo P := by
  rw [primeBase, hr.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hd⟩
    have he : r = q := (Nat.prime_dvd_prime_iff_eq hr (primesUpTo_mem.mp hq).1).mp hd
    simpa only [he] using hq
  · intro h
    exact ⟨r, h, dvd_rfl⟩

theorem supported_iff_smooth {P : ℝ} {n : ℕ} (hn : 0 < n) :
    Supported (primeBase P) n ↔ n ∈ smoothIntegers P := by
  rw [supported_iff_prime_divisors (primeBase_pos P) hn, smoothIntegers_mem]
  constructor
  · intro h
    exact ⟨hn.ne', fun r hr hd => (primesUpTo_mem.mp ((prime_dvd_primeBase hr).mp (h r hr hd))).2⟩
  · rintro ⟨_, h⟩ r hr hd
    exact (prime_dvd_primeBase hr).mpr (primesUpTo_mem.mpr ⟨hr, h r hr hd⟩)

theorem canonical_smooth_part {P : ℝ} {n : ℕ} (hn : 0 < n) :
    supportedPart (primeBase P) n ∈ smoothIntegers P :=
  (supported_iff_smooth (supportedPart_pos hn)).mp (supportedPart_supported hn)

theorem canonical_rough_primes {P : ℝ} {n r : ℕ} (hn : 0 < n)
    (hr : r.Prime) (hd : r ∣ roughPart (primeBase P) n) : P < (r : ℝ) := by
  by_contra h
  have hm : r ∈ primesUpTo P := primesUpTo_mem.mpr ⟨hr, le_of_not_gt h⟩
  have hb : r ∣ primeBase P := (prime_dvd_primeBase hr).mpr hm
  have hg := Nat.dvd_gcd hd hb
  rw [(roughPart_coprime_base (b := primeBase P) hn).gcd_eq_one] at hg
  exact hr.not_dvd_one hg

theorem canonical_decomposition {P : ℝ} {n : ℕ} (hn : 0 < n) :
    roughPart (primeBase P) n * supportedPart (primeBase P) n = n ∧
      supportedPart (primeBase P) n ∈ smoothIntegers P ∧
      ∀ r : ℕ, r.Prime → r ∣ roughPart (primeBase P) n → P < (r : ℝ) :=
  ⟨roughPart_mul_supportedPart hn, canonical_smooth_part hn,
    fun _ hr hd => canonical_rough_primes hn hr hd⟩

theorem steinhaus_smooth_congr {P : ℝ} {n : ℕ} (hn : n ∈ smoothIntegers P)
    {ω ω' : PhaseSpace} (hω : ∀ r ∈ primesUpTo P, ω r = ω' r) :
    steinhaus n ω = steinhaus n ω' := by
  have hn' := smoothIntegers_mem.mp hn
  simp only [steinhaus, if_neg hn'.1]
  apply Finset.prod_congr rfl
  intro r hr
  have hm := Nat.mem_primeFactors.mp hr
  have hs : r ∈ primesUpTo P := primesUpTo_mem.mpr ⟨hm.1, hn'.2 r hm.1 hm.2.1⟩
  unfold phase
  rw [hω r hs]

theorem primeArgument_small_coordinates {P : ℝ} (c1 c2 : ℕ → ℂ)
    {ω ω' : PhaseSpace} (hω : ∀ r ∈ primesUpTo P, ω r = ω' r) :
    primeArgument P c1 c2 (fun n => steinhaus n ω) =
      primeArgument P c1 c2 (fun n => steinhaus n ω') := by
  unfold primeArgument
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hp := (primesUpTo_mem.mp hr).1
  have hv : steinhaus r ω = steinhaus r ω' := by
    rw [steinhaus_prime hp, steinhaus_prime hp]
    unfold phase
    rw [hω r hr]
  simp only [steinhaus_pow, hv]

theorem smoothBox_small_coordinates (p : ℕ) (c1 c2 : Coefficients p) (i : Boxes p)
    {ω ω' : PhaseSpace}
    (hω : ∀ r ∈ primesUpTo (primeCutoff ((p : ℝ)-1)), ω r = ω' r) :
    smoothBox p c1 c2 i (fun n => steinhaus n ω) =
      smoothBox p c1 c2 i (fun n => steinhaus n ω') := by
  have he (j : Fin (factorCount ((p : ℝ)-1))) :=
    primeArgument_small_coordinates (c1 j) (c2 j) hω
  unfold smoothBox HarperProductApproximation.smoothValue
  simp_rw [he]

end NField.Alignment.HarperSmoothRough
