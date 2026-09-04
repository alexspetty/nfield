/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.Definitions

/-!
Clearing-depth and residue-count lemmas for
"Three and the Golden Ratio."
-/

namespace NField.Alignment

/-- Supported denominators are closed under multiplication. -/
theorem supported_mul {b m n : ℕ} (hm : Supported b m) (hn : Supported b n) :
    Supported b (m * n) := by
  rcases hm with ⟨D, hD⟩
  rcases hn with ⟨E, hE⟩
  refine ⟨D + E, ?_⟩
  rw [pow_add]
  exact Nat.mul_dvd_mul hD hE

/-- Every divisor of the base is supported. -/
theorem supported_of_dvd_base {b q : ℕ} (hq : q ∣ b) : Supported b q := by
  exact ⟨1, by simpa using hq⟩

/-- A prime excluded from the base is also excluded from every clearing power. -/
theorem prime_coprime_base_pow {p b D : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    Nat.Coprime p (b ^ D) := by
  exact (hp.coprime_iff_not_dvd.mpr hpb).pow_right D

/-- The cofactor at any valid clearing depth remains coprime to the rough prime. -/
theorem prime_coprime_clearingCofactor {p b m D : ℕ} (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hm : m ∣ b ^ D) :
    Nat.Coprime p (clearingCofactor b m D) := by
  apply Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hm)
  exact prime_coprime_base_pow hp hpb

/-- Exactly one representative of a fixed residue occurs in a complete period. -/
theorem residueCount_one_period {p r : ℕ} (hr : r < p) :
    residueCount p r 1 = 1 := by
  rw [residueCount, Nat.mul_one, Nat.count_eq_card_filter_range]
  have hfilter : (Finset.range p).filter (fun k => k % p = r) = {r} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro h
      rw [Nat.mod_eq_of_lt h.1] at h
      exact h.2
    · intro h
      subst k
      exact ⟨hr, Nat.mod_eq_of_lt hr⟩
  rw [hfilter]
  simp

/-- Every residue occurs exactly `m` times in `m` complete periods. -/
theorem residueCount_eq {p r m : ℕ} (hr : r < p) :
    residueCount p r m = m := by
  induction m with
  | zero => simp [residueCount]
  | succ m ih =>
      rw [residueCount, Nat.mul_succ, Nat.count_add]
      rw [show Nat.count (fun k => (p * m + k) % p = r) p =
          Nat.count (fun k => k % p = r) p by
        congr 1
        funext k
        simp [Nat.add_mod]]
      rw [show Nat.count (fun k => k % p = r) p = 1 by
        simpa [residueCount] using (residueCount_one_period hr)]
      exact congrArg Nat.succ ih

/-- There are `m-1` nonzero multiples of `p` below `p*m`. -/
theorem terminatingNumeratorCount_eq {p m : ℕ} (hp : 0 < p) :
    terminatingNumeratorCount p m = m - 1 := by
  simp [terminatingNumeratorCount, residueCount_eq hp]

/-- There are `m` representatives of residue one below `p*m` when `p>1`. -/
theorem matchingNumeratorCount_eq {p m : ℕ} (hp : 1 < p) :
    matchingNumeratorCount p m = m := by
  exact residueCount_eq hp

/-- The two aligned residue classes contribute exactly `2*m-1` numerators. -/
theorem alignedNumeratorCount_eq {p m : ℕ} (hp : 1 < p) :
    alignedNumeratorCount p m = 2 * m - 1 := by
  rw [alignedNumeratorCount, terminatingNumeratorCount_eq (by omega),
    matchingNumeratorCount_eq hp]
  omega

end NField.Alignment
