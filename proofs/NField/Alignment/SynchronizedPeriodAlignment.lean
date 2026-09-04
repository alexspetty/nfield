/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ThreeTier

/-!
# Synchronized full-period alignment

This module packages the clearing-depth invariance of a synchronized
long-division comparison over one complete multiplicative period. The
definitions and proofs are independent of any manuscript title.
-/

namespace NField.Alignment

open NField.Alignment.ThreeTier

/-- The multiplicative order of the base modulo a coprime prime. -/
noncomputable def primeBasePeriod (b p : ℕ) (hp : p.Prime) (hpb : ¬p ∣ b) : ℕ :=
  orderOf (ZMod.unitOfCoprime b
    (hp.coprime_iff_not_dvd.mpr hpb).symm)

/-- A coprime base has a positive multiplicative period modulo the prime. -/
theorem primeBasePeriod_pos {b p : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) :
    0 < primeBasePeriod b p hp hpb := by
  unfold primeBasePeriod
  exact orderOf_pos (ZMod.unitOfCoprime b
    (hp.coprime_iff_not_dvd.mpr hpb).symm)

/-- Raising the base to its multiplicative period gives residue one. -/
theorem pow_primeBasePeriod_mod_eq_one {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    b ^ primeBasePeriod b p hp hpb % p = 1 % p := by
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime b
    (hp.coprime_iff_not_dvd.mpr hpb).symm
  have hpow : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hcoe : ((u : ZMod p) ^ orderOf u) = 1 := by
    exact congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hpow
  have hcast : ((b ^ orderOf u : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    simpa [u, ZMod.coe_unitOfCoprime] using hcoe
  have hmod := (ZMod.natCast_eq_natCast_iff' (b ^ orderOf u) 1 p).mp hcast
  simpa [primeBasePeriod, u] using hmod

/-- A synchronized average over any complete modular period is independent of
which valid common clearing depth is selected. -/
theorem clearedAlignmentReal_independent_of_clearing_depth_of_period
    {b t m D E L : ℕ} (ht : 0 < t) (hm : 1 ≤ m)
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E)
    (hperiod : b ^ L % t = 1 % t) :
    clearedAlignmentReal b t m D L = clearedAlignmentReal b t m E L := by
  rcases le_total D E with hDE | hED
  · obtain ⟨q, hEq⟩ := Nat.exists_eq_add_of_le hDE
    subst E
    exact (ThreeTier.clearedAlignmentReal_independent_of_later_clearing_depth
      (b := b) (t := t) (m := m) (D := D) (q := q) (L := L)
      ht hm hD hperiod).symm
  · obtain ⟨q, hEq⟩ := Nat.exists_eq_add_of_le hED
    subst D
    exact ThreeTier.clearedAlignmentReal_independent_of_later_clearing_depth
      (b := b) (t := t) (m := m) (D := E) (q := q) (L := L)
      ht hm hE hperiod

/-- The literal synchronized average over the prime's multiplicative period is
independent of which valid common clearing depth is selected. -/
theorem clearedAlignmentReal_independent_of_clearing_depth
    {b p m D E : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    clearedAlignmentReal b p m D (primeBasePeriod b p hp hpb) =
      clearedAlignmentReal b p m E (primeBasePeriod b p hp hpb) :=
  clearedAlignmentReal_independent_of_clearing_depth_of_period
    hp.pos hm hD hE (pow_primeBasePeriod_mod_eq_one hp hpb)

/-- In the one-digit regime, the literal denominator-clock average is exactly
the closed real alignment formula. -/
theorem clearedOneDigitAlignmentReal_eq
    {b p m D : ℕ} (hp : p.Prime) (hb : 2 ≤ b)
    (hpb : ¬p ∣ b) (hmod : b % p = 1)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b p m D 1 =
      NField.Golden.alignmentFormulaReal p m := by
  have hle : p ≤ b + 1 := by
    by_contra hnot
    have hbp : b < p := by omega
    have hbmod : b % p = b := Nat.mod_eq_of_lt hbp
    omega
  rw [ThreeTier.clearedAlignmentReal_eq_canonicalRoughAlignmentReal
    hp.pos hm hD]
  unfold ThreeTier.canonicalRoughAlignmentReal
  rw [if_neg hp.ne_one]
  exact ThreeTier.synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    hp hpb (digitPartitioning_of_le hp.pos hpb hle)
      (prime_coprime_clearingCofactor hp hpb hD) hm (by norm_num)

end NField.Alignment
