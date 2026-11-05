/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DigitPartitioning
import NField.Alignment.SupportedDenominators

/-!
# One-digit blocks for an integer modulus

The residue partition used by the weighted golden-scale profile does not need
primality.  This module records the generic modulus statement without changing
the historical prime-specific formalization.
-/

namespace NField.Alignment

open NField.CollisionDefinition

/-- At a common clearing depth, this is literal equality with the reference
one-digit tail.  Termination is deliberately not included. -/
def MatchesOneDigitReference (b q u k : ℕ) : Prop :=
  digitBin b q ((k * u) % q) = digitBin b q (u % q)

/-- Congruence of the base to one makes the modulus coprime to the base. -/
theorem modulus_coprime_base_of_mod_one {b q : ℕ} (hq : 1 < q)
    (hmod : b % q = 1) : Nat.Coprime q b := by
  have hmeq : b * 1 ≡ 1 [MOD q] := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hq] using hmod
  exact (Nat.coprime_of_mul_modEq_one 1 hmeq).symm

/-- A valid clearing cofactor is a unit modulo an arbitrary modulus coprime to
the base. -/
theorem modulus_coprime_clearingCofactor {b q m D : ℕ}
    (hcop : Nat.Coprime q b) (hm : m ∣ b ^ D) :
    Nat.Coprime q (clearingCofactor b m D) := by
  apply Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hm)
  exact hcop.pow_right D

/-- When `b` is one modulo `q`, a residue `r` produces the digit
`(b / q) * r`. -/
theorem digitBin_eq_scale_modulus {b q r : ℕ} (hq : 0 < q) (hr : r < q)
    (hmod : b % q = 1) :
    digitBin b q r = (b / q) * r := by
  have hb0 := Nat.mod_add_div b q
  have hb : b = 1 + q * (b / q) := by omega
  unfold digitBin
  calc
    (b * r) / q = ((1 + q * (b / q)) * r) / q :=
      congrArg (fun x => (x * r) / q) hb
    _ = (r + q * ((b / q) * r)) / q := by congr 1; ring
    _ = r / q + (b / q) * r := Nat.add_mul_div_left r ((b / q) * r) hq
    _ = (b / q) * r := by rw [Nat.div_eq_of_lt hr, zero_add]

/-- The one-digit map is injective on all residue representatives. -/
theorem digitBin_injective_mod_one {b q r s : ℕ} (hq : 0 < q)
    (hb : 1 < b) (hr : r < q) (hs : s < q) (hmod : b % q = 1)
    (h : digitBin b q r = digitBin b q s) : r = s := by
  rw [digitBin_eq_scale_modulus hq hr hmod,
    digitBin_eq_scale_modulus hq hs hmod] at h
  have hb0 := Nat.mod_add_div b q
  have hscale : 0 < b / q := by
    have hprod : 0 < q * (b / q) := by omega
    exact Nat.pos_of_mul_pos_left hprod
  exact Nat.eq_of_mul_eq_mul_left hscale h

/-- Every later digit repeats the first digit when `b` is one modulo `q`. -/
theorem digitAt_eq_initial_modulus {b q r j : ℕ}
    (hq : 1 < q) (hmod : b % q = 1) :
    digitAt b q r j = digitBin b q (r % q) := by
  unfold digitAt
  have hpow : b ^ j % q = 1 := by
    rw [Nat.pow_mod, hmod]
    simp [Nat.mod_eq_of_lt hq]
  rw [Nat.mul_mod, hpow]
  simp

/-- Literal matching is exactly the reference residue class for every integer
modulus. -/
theorem matchesOneDigitReference_iff_residue_one
    {b q u k : ℕ} (hq : 1 < q) (hb : 2 ≤ b) (hmod : b % q = 1)
    (hu : Nat.Coprime q u) :
    MatchesOneDigitReference b q u k ↔ k % q = 1 := by
  constructor
  · intro h
    unfold MatchesOneDigitReference at h
    have hku : (k * u) % q < q := Nat.mod_lt _ (by omega)
    have hu' : u % q < q := Nat.mod_lt _ (by omega)
    have hres : (k * u) % q = u % q :=
      digitBin_injective_mod_one (by omega) (by omega) hku hu' hmod h
    have hmul : k * u ≡ 1 * u [MOD q] := by
      simpa [Nat.ModEq] using hres
    have hcancel := Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one hmul
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hq] using hcancel
  · intro hone
    unfold MatchesOneDigitReference
    congr 1
    calc
      (k * u) % q = ((k % q) * (u % q)) % q := by simp [Nat.mul_mod]
      _ = u % q := by simp [hone]

/-- A numerator clears at depth `D` in the denominator presentation `q*m`. -/
def ClearsAtDepth (b q m D k : ℕ) : Prop :=
  q * m ∣ k * b ^ D

/-- At a common clearing depth, termination is exactly residue zero for every
integer modulus coprime to the base. -/
theorem clearsAtDepth_iff_residue_zero {b q m D k : ℕ}
    (hcop : Nat.Coprime q b) (hm : m ∣ b ^ D) :
    ClearsAtDepth b q m D k ↔ k % q = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro hclear
    have hqQm : q ∣ q * m := dvd_mul_right q m
    have hqProduct : q ∣ k * b ^ D := hqQm.trans hclear
    exact (hcop.pow_right D).dvd_of_dvd_mul_right hqProduct
  · intro hqk
    rcases hqk with ⟨a, rfl⟩
    rcases hm with ⟨u, hu⟩
    refine ⟨a * u, ?_⟩
    rw [hu]
    ring

/-- The residue classes below `q*m` have the block sizes used in the finite
profile. -/
theorem oneDigit_modulus_block_counts {q m : ℕ} (hq : 1 < q) :
    terminatingNumeratorCount q m = m - 1 ∧
      matchingNumeratorCount q m = m ∧
      Nat.count (fun k => k % q ≠ 0 ∧ k % q ≠ 1) (q * m) =
        (q - 2) * m := by
  have hzero := terminatingNumeratorCount_eq (p := q) (m := m) (by omega)
  have hone := matchingNumeratorCount_eq (p := q) (m := m) hq
  constructor
  · exact hzero
  constructor
  · exact hone
  · have htotal :
        Nat.count (fun k => k % q = 0 ∨ k % q = 1) (q * m) = 2 * m := by
      rw [Nat.count_eq_card_filter_range, Finset.filter_or,
        Finset.card_union_of_disjoint]
      · rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
        rw [show Nat.count (fun k => k % q = 0) (q * m) =
            residueCount q 0 m by rfl,
          show Nat.count (fun k => k % q = 1) (q * m) =
            residueCount q 1 m by rfl,
          residueCount_eq (by omega), residueCount_eq hq]
        omega
      · rw [Finset.disjoint_left]
        intro k hk0 hk1
        simp only [Finset.mem_filter] at hk0 hk1
        omega
    have hpartition := Finset.card_filter_add_card_filter_not
      (fun k : ℕ => k % q = 0 ∨ k % q = 1)
      (s := Finset.range (q * m))
    rw [← Nat.count_eq_card_filter_range,
      ← Nat.count_eq_card_filter_range, htotal] at hpartition
    simp only [not_or, Finset.card_range] at hpartition
    have hcount :
        Nat.count (fun k => k % q ≠ 0 ∧ k % q ≠ 1) (q * m) =
          q * m - 2 * m := by
      apply Nat.eq_sub_of_add_eq
      simpa [Nat.add_comm] using hpartition
    calc
      Nat.count (fun k => k % q ≠ 0 ∧ k % q ≠ 1) (q * m) =
          q * m - 2 * m := hcount
      _ = (q - 2) * m := (Nat.sub_mul q 2 m).symm

/-- The complete generic certificate at a chosen common clearing depth. -/
theorem oneDigit_modulus_certificate {b q m D : ℕ}
    (hq : 1 < q) (hb : 2 ≤ b) (hmod : b % q = 1)
    (hm : m ∣ b ^ D) :
    (∀ k : ℕ, ClearsAtDepth b q m D k ↔ k % q = 0) ∧
      (∀ k : ℕ,
        MatchesOneDigitReference b q (clearingCofactor b m D) k ↔
          k % q = 1) ∧
      terminatingNumeratorCount q m = m - 1 ∧
      matchingNumeratorCount q m = m ∧
      Nat.count (fun k => k % q ≠ 0 ∧ k % q ≠ 1) (q * m) =
        (q - 2) * m := by
  have hcop := modulus_coprime_base_of_mod_one hq hmod
  have hu := modulus_coprime_clearingCofactor hcop hm
  refine ⟨fun k => clearsAtDepth_iff_residue_zero hcop hm,
    fun k => matchesOneDigitReference_iff_residue_one hq hb hmod hu, ?_⟩
  exact oneDigit_modulus_block_counts hq

/-- Changing the common clearing depth preserves both the terminating block
and literal matching with the reference tail. -/
theorem oneDigit_profile_independent_depth {b q m D E : ℕ}
    (hq : 1 < q) (hb : 2 ≤ b) (hmod : b % q = 1)
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    (∀ k : ℕ, ClearsAtDepth b q m D k ↔ ClearsAtDepth b q m E k) ∧
      (∀ k : ℕ,
        MatchesOneDigitReference b q (clearingCofactor b m D) k ↔
          MatchesOneDigitReference b q (clearingCofactor b m E) k) := by
  have left := oneDigit_modulus_certificate hq hb hmod hD
  have right := oneDigit_modulus_certificate hq hb hmod hE
  exact ⟨fun k => (left.1 k).trans (right.1 k).symm,
    fun k => (left.2.1 k).trans (right.2.1 k).symm⟩

end NField.Alignment
