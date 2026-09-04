/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitPrime

/-!
# Literal synchronized one-digit alignment

This module closes the semantic bridge between the manuscript's average over
the actual numerator range and the residue-count formula.  The common clearing
depth remains explicit all the way to the final rational alignment.
-/

namespace NField.Alignment

open NField.CollisionDefinition

/-- Exact arithmetic complement identity behind the pairing of `k/n` with
`(n-k)/n`. -/
theorem rationalFractionComplement (k n : ℚ) (hn : n ≠ 0) :
    k / n + (n - k) / n = 1 := by
  field_simp
  ring

/-- For positive denominators and nonzero bases, the common-clearing-power
definition is equivalent to the manuscript's prime-factor formulation. -/
theorem supported_iff_every_prime_divisor_divides_base
    {b m : ℕ} (hb : 0 < b) (hm : 0 < m) :
    Supported b m ↔ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ b := by
  constructor
  · rintro ⟨D, hD⟩ q hq hqm
    exact hq.dvd_of_dvd_pow (hqm.trans hD)
  · intro hprime
    rw [Supported, Nat.exists_dvd_pow_iff hm.ne' hb.ne']
    intro q hqm
    have hq := Nat.mem_primeFactors.mp hqm
    exact hq.1.mem_primeFactors (hprime q hq.1 hq.2.1) hb.ne'

/-- Decimal supported denominators are exactly products of powers of two and
five. -/
theorem base_ten_supported_iff_two_pow_mul_five_pow
    {m : ℕ} (hm : 0 < m) :
    Supported 10 m ↔ ∃ a c : ℕ, m = 2 ^ a * 5 ^ c := by
  constructor
  · intro hsupported
    have hprime := (supported_iff_every_prime_divisor_divides_base
      (b := 10) (m := m) (by norm_num) hm).mp hsupported
    let a := m.factorization 2
    let c := m.factorization 5
    refine ⟨a, c, ?_⟩
    apply Nat.eq_of_factorization_eq hm.ne' (by positivity)
    intro q
    by_cases hq2 : q = 2
    · subst q
      simp [a, c, Nat.factorization_mul,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
    by_cases hq5 : q = 5
    · subst q
      simp [a, c, Nat.factorization_mul,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
    by_cases hqprime : q.Prime
    · have hqnotdvd : ¬q ∣ m := by
        intro hqm
        have hqten : q ∣ 10 := hprime q hqprime hqm
        have hqtwentyfive : q ∣ 2 * 5 := by norm_num at hqten ⊢; exact hqten
        rcases hqprime.dvd_mul.mp hqtwentyfive with hqtwo | hqfive
        · exact hq2 ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp hqtwo)
        · exact hq5 ((Nat.prime_dvd_prime_iff_eq hqprime (by norm_num)).mp hqfive)
      rw [Nat.factorization_eq_zero_of_not_dvd hqnotdvd]
      simp [Nat.factorization_mul,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), hq2, hq5]
    · rw [Nat.factorization_eq_zero_of_not_prime m hqprime]
      simp [Nat.factorization_mul,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), hq2, hq5]
  · rintro ⟨a, c, rfl⟩
    refine ⟨a + c, ?_⟩
    rw [show 10 = 2 * 5 by norm_num, mul_pow]
    refine ⟨2 ^ c * 5 ^ a, ?_⟩
    ring

/-- Arithmetic termination after at most `D` base-`b` digits.  For the rational
`k/n`, this is exactly the divisibility condition `n | k*b^D`. -/
def TerminatesAtDepth (b k n D : ℕ) : Prop :=
  n ∣ k * b ^ D

/-- A rational terminates in base `b` when it terminates at some finite
long-division depth. -/
def TerminatesInBase (b k n : ℕ) : Prop :=
  ∃ D : ℕ, TerminatesAtDepth b k n D

/-- The common-clearing-power definition is exactly the arithmetic statement
that `1/m` terminates after finitely many base-`b` digits. -/
theorem supported_iff_one_terminates_at_some_depth {b m : ℕ} :
    Supported b m ↔ TerminatesInBase b 1 m := by
  simp [Supported, TerminatesInBase, TerminatesAtDepth]

/-- At a valid common clearing depth, `k/(p*m)` terminates exactly when its
numerator is zero modulo the rough prime. -/
theorem terminatesAtDepth_iff_residue_zero
    {b p m D k : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hm : m ∣ b ^ D) :
    TerminatesAtDepth b k (p * m) D ↔ k % p = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro hterm
    have hpPm : p ∣ p * m := dvd_mul_right p m
    have hpProduct : p ∣ k * b ^ D := hpPm.trans hterm
    rcases hp.dvd_mul.mp hpProduct with hpk | hpPow
    · exact hpk
    · exact False.elim (hpb (hp.dvd_of_dvd_pow hpPow))
  · intro hpk
    rcases hpk with ⟨q, rfl⟩
    rcases hm with ⟨u, hu⟩
    refine ⟨q * u, ?_⟩
    rw [hu]
    ring

/-- For a supported denominator times a rough prime, termination at any depth
is equivalent to the numerator being zero modulo that prime. -/
theorem terminatesInBase_iff_residue_zero
    {b p m k : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hm : Supported b m) :
    TerminatesInBase b k (p * m) ↔ k % p = 0 := by
  constructor
  · rintro ⟨D, hterm⟩
    rw [← Nat.dvd_iff_mod_eq_zero]
    have hpPm : p ∣ p * m := dvd_mul_right p m
    have hpProduct : p ∣ k * b ^ D := hpPm.trans hterm
    rcases hp.dvd_mul.mp hpProduct with hpk | hpPow
    · exact hpk
    · exact False.elim (hpb (hp.dvd_of_dvd_pow hpPow))
  · intro hk
    rcases hm with ⟨D, hD⟩
    exact ⟨D, (terminatesAtDepth_iff_residue_zero hp hpb hD).2 hk⟩

/-- Literal number of aligned numerators in the manuscript's range
`1, ..., p*m-1`, expressed as a count below `p*m` with the always-aligned zero
representative removed. -/
noncomputable def synchronizedAlignedNumeratorCount (b p m D : ℕ) : ℕ := by
  classical
  exact Nat.count
    (fun k => synchronizedAligned b p (clearingCofactor b m D) k)
    (p * m) - 1

/-- The manuscript's one-digit synchronized average at a chosen valid common
clearing depth. -/
noncomputable def synchronizedOneDigitAlignment (b p m D : ℕ) : ℚ :=
  (synchronizedAlignedNumeratorCount b p m D : ℚ) /
    ((p * m - 1 : ℕ) : ℚ)

theorem residue_zero_one_count {p m : ℕ} (hp : 1 < p) :
    Nat.count (fun k => k % p = 0 ∨ k % p = 1) (p * m) = 2 * m := by
  rw [Nat.count_eq_card_filter_range, Finset.filter_or,
    Finset.card_union_of_disjoint]
  · rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
    rw [show Nat.count (fun k => k % p = 0) (p * m) =
        residueCount p 0 m by rfl,
      show Nat.count (fun k => k % p = 1) (p * m) =
        residueCount p 1 m by rfl,
      residueCount_eq (by omega), residueCount_eq hp]
    omega
  · rw [Finset.disjoint_left]
    intro k hk0 hk1
    simp only [Finset.mem_filter] at hk0 hk1
    omega

/-- The literal synchronized count is exactly `2*m-1`. -/
theorem synchronizedAlignedNumeratorCount_eq
    {b p m D : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1) (hm : m ∣ b ^ D) :
    synchronizedAlignedNumeratorCount b p m D = 2 * m - 1 := by
  classical
  unfold synchronizedAlignedNumeratorCount
  simp_rw [synchronizedAligned_at_clearing_iff hp hb hpb hmod hm]
  rw [residue_zero_one_count hp.one_lt]

/-- The literal synchronized average is independent of the valid clearing
depth. -/
theorem synchronizedOneDigitAlignment_independent_of_clearing_depth
    {b p m D E : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1)
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    synchronizedOneDigitAlignment b p m D =
      synchronizedOneDigitAlignment b p m E := by
  unfold synchronizedOneDigitAlignment
  rw [synchronizedAlignedNumeratorCount_eq hp hb hpb hmod hD,
    synchronizedAlignedNumeratorCount_eq hp hb hpb hmod hE]

/-- Exact formula for the manuscript's literal synchronized average. -/
theorem synchronizedOneDigitAlignment_eq
    {b p m D : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1) (hm : m ∣ b ^ D) :
    synchronizedOneDigitAlignment b p m D =
      ((2 * m - 1 : ℕ) : ℚ) / ((p * m - 1 : ℕ) : ℚ) := by
  unfold synchronizedOneDigitAlignment
  rw [synchronizedAlignedNumeratorCount_eq hp hb hpb hmod hm]

/-- The older reusable closed form is definitionally equal to the literal
manuscript average at every valid clearing depth. -/
theorem synchronizedOneDigitAlignment_eq_oneDigitAlignment
    {b p m D : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1) (hm : m ∣ b ^ D) :
    synchronizedOneDigitAlignment b p m D = oneDigitAlignment p m := by
  rw [synchronizedOneDigitAlignment_eq hp hb hpb hmod hm,
    oneDigitAlignment_eq hp]

/-- Literal count of nonterminating positive numerators below `p*m`. -/
def nonterminatingNumeratorCountLiteral (p m : ℕ) : ℕ :=
  Nat.count (fun k => k % p ≠ 0) (p * m)

/-- Literal count of aligned nonterminating positive numerators. -/
def alignedNonterminatingNumeratorCount (p m : ℕ) : ℕ :=
  Nat.count (fun k => k % p = 1) (p * m)

theorem nonterminatingNumeratorCountLiteral_eq
    {p m : ℕ} (hp : 1 < p) :
    nonterminatingNumeratorCountLiteral p m = m * (p - 1) := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range (p * m)) (fun k => k % p = 0)
  have hzero :
      ((Finset.range (p * m)).filter (fun k => k % p = 0)).card = m := by
    rw [← Nat.count_eq_card_filter_range]
    exact residueCount_eq (by omega)
  have hshape : p * m = m + m * (p - 1) := by
    calc
      p * m = (1 + (p - 1)) * m := by congr 1; omega
      _ = m + m * (p - 1) := by ring
  have hpartition' :
      ((Finset.range (p * m)).filter (fun k => k % p = 0)).card +
        ((Finset.range (p * m)).filter (fun k => k % p ≠ 0)).card =
          p * m := by
    simpa only [Finset.card_range] using hpartition
  unfold nonterminatingNumeratorCountLiteral
  rw [Nat.count_eq_card_filter_range]
  rw [hzero] at hpartition'
  omega

theorem alignedNonterminatingNumeratorCount_eq
    {p m : ℕ} (hp : 1 < p) :
    alignedNonterminatingNumeratorCount p m = m := by
  unfold alignedNonterminatingNumeratorCount
  exact residueCount_eq hp

/-- Actual nonterminating-only synchronized alignment. -/
noncomputable def nonterminatingOneDigitAlignment (p m : ℕ) : ℚ :=
  (alignedNonterminatingNumeratorCount p m : ℚ) /
    (nonterminatingNumeratorCountLiteral p m : ℚ)

/-- Excluding terminating fractions gives exactly `1/(p-1)`, independently
of the positive supported multiplicity. -/
theorem nonterminatingOneDigitAlignment_eq
    {p m : ℕ} (hp : 1 < p) (hm : 1 ≤ m) :
    nonterminatingOneDigitAlignment p m = 1 / ((p - 1 : ℕ) : ℚ) := by
  rw [nonterminatingOneDigitAlignment,
    alignedNonterminatingNumeratorCount_eq hp,
    nonterminatingNumeratorCountLiteral_eq hp]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpQ : ((p - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show p - 1 ≠ 0 by omega)
  push_cast
  field_simp [hmQ, hpQ]

theorem nonterminatingOneDigitAlignment_prime_three {m : ℕ} (hm : 1 ≤ m) :
    nonterminatingOneDigitAlignment 3 m = 1 / 2 := by
  rw [nonterminatingOneDigitAlignment_eq (by norm_num) hm]
  norm_num

/-- Every exact rational entry in the manuscript's displayed base-ten table. -/
theorem prime_three_displayed_alignment_values :
    oneDigitAlignment 3 1 = 1 / 2 ∧
    oneDigitAlignment 3 2 = 3 / 5 ∧
    oneDigitAlignment 3 4 = 7 / 11 ∧
    oneDigitAlignment 3 5 = 9 / 14 ∧
    oneDigitAlignment 3 8 = 15 / 23 ∧
    oneDigitAlignment 3 10 = 19 / 29 ∧
    oneDigitAlignment 3 16 = 31 / 47 ∧
    oneDigitAlignment 3 32 = 63 / 95 ∧
    oneDigitAlignment 3 100 = 199 / 299 ∧
    oneDigitAlignment 3 256 = 511 / 767 := by
  repeat' apply And.intro
  all_goals rw [oneDigitAlignment_eq Nat.prime_three]
  all_goals norm_num

/-- A displayed decimal is a correct four-place rounding when its distance
from the exact rational value is at most half of one unit in the fourth
decimal place. -/
def WithinFourDecimalRounding (exact displayed : ℚ) : Prop :=
  |exact - displayed| ≤ 1 / 20000

/-- Every decimal printed in the alignment table is the correct four-place
rounding of its exact rational entry. -/
theorem prime_three_displayed_decimal_roundings :
    WithinFourDecimalRounding (oneDigitAlignment 3 1) (5000 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 2) (6000 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 4) (6364 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 5) (6429 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 8) (6522 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 10) (6552 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 16) (6596 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 32) (6632 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 100) (6656 / 10000) ∧
    WithinFourDecimalRounding (oneDigitAlignment 3 256) (6662 / 10000) := by
  repeat' apply And.intro
  all_goals rw [oneDigitAlignment_eq Nat.prime_three]
  all_goals norm_num [WithinFourDecimalRounding, abs_of_nonneg, abs_of_nonpos]

/-- At a valid base-ten clearing cofactor, residue two produces the nines
complement of the reference digit. -/
theorem base_ten_residue_two_is_nines_complement
    {u : ℕ} (hu : Nat.Coprime 3 u) :
    digitBin 10 3 ((2 * u) % 3) + digitBin 10 3 (u % 3) = 9 := by
  have hult : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hune : u % 3 ≠ 0 := by
    intro hzero
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hu)
      (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hcases : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hcases with h | h <;>
    simp [digitBin, Nat.mul_mod, h]

end NField.Alignment
