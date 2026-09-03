/-
Author: Alexander S. Petty
-/

import Mathlib
import NField.Alignment.Definitions

/-!
# Supported prime-exponent coordinates

The supported positive integers are the nonnegative prime-exponent cone on the
prime divisors of the base.  This module records the precise arithmetic content
behind that statement: support is characterized prime by prime, factorization
is additive under multiplication, reconstructs the integer, and is injective.
-/

namespace NField.Alignment.SupportedPrimeExponentCone

open NField.Alignment

/-- Positive supported integers, the manuscript's multiplicative domain. -/
def SupportedPositive (b : ℕ) :=
  {m : ℕ // 0 < m ∧ Supported b m}

/-- Nonnegative prime-exponent coordinates supported on the prime divisors of
the base. -/
def PrimeExponentCone (b : ℕ) :=
  {e : ℕ →₀ ℕ // e.support ⊆ b.primeFactors}

/-- Integer prime-exponent coordinates, the additive group completion of the
nonnegative cone. -/
def PrimeExponentGroup (b : ℕ) :=
  {e : ℕ →₀ ℤ // e.support ⊆ b.primeFactors}

/-- Embed a nonnegative exponent vector in the integer exponent group. -/
noncomputable def exponentNatCast (e : ℕ →₀ ℕ) : ℕ →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) e

/-- Positive part of an integer exponent vector. -/
noncomputable def exponentPositivePart (e : ℕ →₀ ℤ) : ℕ →₀ ℕ :=
  Finsupp.mapRange Int.toNat (by simp) e

/-- Negative part of an integer exponent vector. -/
noncomputable def exponentNegativePart (e : ℕ →₀ ℤ) : ℕ →₀ ℕ :=
  Finsupp.mapRange (fun z : ℤ => (-z).toNat) (by simp) e

/-- Evaluate a nonnegative prime-exponent vector as a positive integer. -/
def naturalExponentValue (e : ℕ →₀ ℕ) : ℕ :=
  e.prod (fun q k => q ^ k)

/-- A supported positive integer has no prime divisor outside the base. -/
theorem prime_dvd_base_of_supported {b m q : ℕ} (hm : Supported b m)
    (hq : q.Prime) (hqm : q ∣ m) : q ∣ b := by
  rcases hm with ⟨D, hD⟩
  exact hq.dvd_of_dvd_pow (dvd_trans hqm hD)

/-- If every prime divisor of a positive integer divides the positive base,
then the integer divides a power of the base. -/
theorem supported_of_prime_divisors {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b) : Supported b m := by
  refine ⟨m, ?_⟩
  rw [← Nat.factorization_le_iff_dvd hm.ne' (pow_ne_zero _ hb.ne')]
  rw [Nat.factorization_pow]
  intro q
  by_cases hmq : m.factorization q = 0
  · simp [hmq]
  · have hqmem : q ∈ m.primeFactors := by
      simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hmq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqm : q ∣ m := (Nat.mem_primeFactors.mp hqmem).2.1
    have hqb : q ∣ b := hprime q hqprime hqm
    have hbq : 0 < b.factorization q :=
      hqprime.factorization_pos_of_dvd hb.ne' hqb
    have hlt : m.factorization q < m := Nat.factorization_lt q hm.ne'
    change m.factorization q ≤ m * b.factorization q
    nlinarith

/-- Divisibility by a base power is equivalent to having only prime divisors
from the base.  This is the manuscript's two formulations of support. -/
theorem supported_iff_prime_divisors {b m : ℕ} (hb : 0 < b) (hm : 0 < m) :
    Supported b m ↔ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b := by
  exact ⟨fun hs q hq hqm => prime_dvd_base_of_supported hs hq hqm,
    supported_of_prime_divisors hb hm⟩

/-- The support of the factorization coordinate lies in the base's prime
support exactly when the integer is supported. -/
theorem supported_iff_factorization_support_subset {b m : ℕ}
    (hb : 0 < b) (hm : 0 < m) :
    Supported b m ↔ m.factorization.support ⊆ b.primeFactors := by
  rw [supported_iff_prime_divisors hb hm]
  constructor
  · intro h q hqmem
    have hqprime : q.Prime := by
      exact Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hqmem)
    have hqm : q ∣ m := by
      exact (Nat.mem_primeFactors.mp (by
        simpa [Nat.support_factorization] using hqmem)
        ).2.1
    exact Nat.mem_primeFactors.mpr ⟨hqprime, h q hqprime hqm, hb.ne'⟩
  · intro h q hqprime hqm
    have hqmem : q ∈ m.factorization.support := by
      simpa [Nat.support_factorization] using
        (Nat.mem_primeFactors.mpr ⟨hqprime, hqm, hm.ne'⟩)
    have : q ∈ b.primeFactors := h hqmem
    exact (Nat.mem_primeFactors.mp this).2.1

/-- Prime factorization reconstructs every positive supported coordinate. -/
theorem prime_exponent_reconstruction {m : ℕ} (hm : 0 < m) :
    m.factorization.prod (fun q e => q ^ e) = m := by
  exact Nat.prod_factorization_pow_eq_self hm.ne'

/-- A ratio of positive integers is recovered exactly from the corresponding
pair of nonnegative exponent coordinates. -/
theorem prime_exponent_ratio_reconstruction {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    ((naturalExponentValue m.factorization : ℕ) : ℚ) /
        (naturalExponentValue n.factorization : ℕ) =
      (m : ℚ) / n := by
  simp only [naturalExponentValue, Nat.prod_factorization_pow_eq_self hm.ne',
    Nat.prod_factorization_pow_eq_self hn.ne']

/-- Multiplication adds prime-exponent coordinates. -/
theorem prime_exponent_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (m * n).factorization = m.factorization + n.factorization := by
  exact Nat.factorization_mul hm.ne' hn.ne'

/-- The prime-exponent coordinate is injective on positive integers. -/
theorem prime_exponent_injective {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m.factorization = n.factorization) : m = n := by
  calc
    m = m.factorization.prod (fun q e => q ^ e) :=
      (prime_exponent_reconstruction hm).symm
    _ = n.factorization.prod (fun q e => q ^ e) := by rw [h]
    _ = n := prime_exponent_reconstruction hn

/-- The supported positive integers are exactly the nonnegative
prime-exponent cone on the primes dividing the base. -/
noncomputable def supportedPrimeExponentEquiv (b : ℕ) (hb : 0 < b) :
    SupportedPositive b ≃ PrimeExponentCone b where
  toFun m :=
    ⟨m.1.factorization,
      (supported_iff_factorization_support_subset hb m.2.1).mp m.2.2⟩
  invFun e := by
    let value := e.1.prod (fun q k => q ^ k)
    have hprime : ∀ q ∈ e.1.support, q.Prime := by
      intro q hq
      exact Nat.prime_of_mem_primeFactors (e.2 hq)
    have hpos : 0 < value := by
      exact Nat.prod_pow_pos_of_zero_notMem_support
        (fun hzero => Nat.not_prime_zero (hprime 0 hzero))
    refine ⟨value, hpos, ?_⟩
    rw [supported_iff_factorization_support_subset hb hpos]
    rw [Nat.prod_pow_factorization_eq_self hprime]
    exact e.2
  left_inv m := by
    apply Subtype.ext
    exact Nat.prod_factorization_pow_eq_self m.2.1.ne'
  right_inv e := by
    apply Subtype.ext
    exact Nat.prod_pow_factorization_eq_self
      (fun q hq => Nat.prime_of_mem_primeFactors (e.2 hq))

/-- Every integer exponent vector is a difference of two vectors in the
nonnegative cone.  This is the concrete group-completion statement used for
rational intervals. -/
theorem primeExponentGroup_eq_difference (b : ℕ) (z : PrimeExponentGroup b) :
    ∃ x y : PrimeExponentCone b,
      exponentNatCast x.1 - exponentNatCast y.1 = z.1 := by
  have hxSupport : (exponentPositivePart z.1).support ⊆ b.primeFactors :=
    (Finsupp.support_mapRange.trans z.2)
  have hySupport : (exponentNegativePart z.1).support ⊆ b.primeFactors :=
    (Finsupp.support_mapRange.trans z.2)
  refine ⟨⟨exponentPositivePart z.1, hxSupport⟩,
    ⟨exponentNegativePart z.1, hySupport⟩, ?_⟩
  ext q
  simp [exponentNatCast, exponentPositivePart, exponentNegativePart]

/-- The manuscript's Pythagorean and five-limit bases have exactly the stated
prime-coordinate supports. -/
theorem baseTwelve_and_baseThirty_prime_supports :
    (∀ q : ℕ, q.Prime → (q ∣ 12 ↔ q = 2 ∨ q = 3)) ∧
      (∀ q : ℕ, q.Prime → (q ∣ 30 ↔ q = 2 ∨ q = 3 ∨ q = 5)) := by
  constructor
  · intro q hq
    constructor
    · intro hdiv
      have hprod : q ∣ 3 * 4 := by norm_num at hdiv ⊢; exact hdiv
      rcases hq.dvd_mul.mp hprod with h3 | h4
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3)
      · have h2pow : q ∣ 2 ^ 2 := by norm_num at h4 ⊢; exact h4
        have h2 : q ∣ 2 := hq.dvd_of_dvd_pow h2pow
        exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
    · rintro (rfl | rfl) <;> norm_num
  · intro q hq
    constructor
    · intro hdiv
      have hprod : q ∣ 2 * (3 * 5) := by norm_num at hdiv ⊢; exact hdiv
      rcases hq.dvd_mul.mp hprod with h2 | hrest
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
      · rcases hq.dvd_mul.mp hrest with h3 | h5
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3))
        · exact Or.inr (Or.inr
            ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5))
    · rintro (rfl | rfl | rfl) <;> norm_num

/-- Under the equivalence, multiplication of supported integers is addition
of their exponent coordinates. -/
theorem supportedPrimeExponentEquiv_mul {b m n : ℕ} (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) (hsm : Supported b m) (hsn : Supported b n) :
    (supportedPrimeExponentEquiv b hb
        ⟨m * n, Nat.mul_pos hm hn, by
          rcases hsm with ⟨D, hD⟩
          rcases hsn with ⟨E, hE⟩
          exact ⟨D + E, by simpa [pow_add] using Nat.mul_dvd_mul hD hE⟩⟩).1 =
      (supportedPrimeExponentEquiv b hb ⟨m, hm, hsm⟩).1 +
        (supportedPrimeExponentEquiv b hb ⟨n, hn, hsn⟩).1 := by
  exact Nat.factorization_mul hm.ne' hn.ne'

/-- Supported multiplication corresponds exactly to addition in the
nonnegative prime-exponent cone. -/
theorem supported_prime_exponent_certificate {b m n : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hn : 0 < n)
    (hsm : Supported b m) (hsn : Supported b n) :
    Supported b (m * n) ∧
      (m * n).factorization = m.factorization + n.factorization ∧
      (m * n).factorization.support ⊆ b.primeFactors := by
  have hmul : Supported b (m * n) := by
    rcases hsm with ⟨D, hD⟩
    rcases hsn with ⟨E, hE⟩
    exact ⟨D + E, by simpa [pow_add] using Nat.mul_dvd_mul hD hE⟩
  exact ⟨hmul, prime_exponent_mul hm hn,
    (supported_iff_factorization_support_subset hb (Nat.mul_pos hm hn)).mp hmul⟩

/-- A larger base containing the old base preserves every supported integer. -/
theorem supported_mono_of_dvd_base {a b m : ℕ} (hab : a ∣ b)
    (hm : Supported a m) : Supported b m := by
  rcases hm with ⟨D, hD⟩
  exact ⟨D, dvd_trans hD (pow_dvd_pow_of_dvd hab D)⟩

/-- Bases 6, 12, and 24 have exactly the same supported positive integers. -/
theorem bases_six_twelve_twentyfour_same_support {m : ℕ} :
    (Supported 6 m ↔ Supported 12 m) ∧
      (Supported 12 m ↔ Supported 24 m) := by
  constructor
  · constructor
    · exact supported_mono_of_dvd_base (by norm_num)
    · rintro ⟨D, hD⟩
      refine ⟨2 * D, dvd_trans hD ?_⟩
      refine ⟨3 ^ D, ?_⟩
      rw [← mul_pow, show 12 * 3 = 6 ^ 2 by norm_num, pow_mul]
  · constructor
    · exact supported_mono_of_dvd_base (by norm_num)
    · rintro ⟨D, hD⟩
      refine ⟨2 * D, dvd_trans hD ?_⟩
      refine ⟨6 ^ D, ?_⟩
      rw [← mul_pow, show 24 * 6 = 12 ^ 2 by norm_num, pow_mul]

/-- Base ten supports its two prime generators but not the missing prime
three, so the Pythagorean fifth direction is absent. -/
theorem base_ten_support_boundary :
    Supported 10 2 ∧ Supported 10 5 ∧ Supported 10 4 ∧ ¬Supported 10 3 := by
  constructor
  · exact ⟨1, by norm_num⟩
  constructor
  · exact ⟨1, by norm_num⟩
  constructor
  · exact ⟨2, by norm_num⟩
  · intro h
    exact (by norm_num : ¬3 ∣ 10)
      (prime_dvd_base_of_supported h Nat.prime_three (by norm_num))

/-- Every base divisible by thirty contains the entire five-limit supported
submonoid. -/
theorem five_limit_submonoid_of_thirty_dvd {b m : ℕ} (hb : 30 ∣ b)
    (hm : Supported 30 m) : Supported b m :=
  supported_mono_of_dvd_base hb hm

end NField.Alignment.SupportedPrimeExponentCone
