/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DigitPartitioning

/-!
# Synchronized field alignment for Digit-Partitioning Primes and the Alignment Formula

The proof below uses the paper's common long-division clock.  It proves the
position-by-position residue classification, its independence from clearing
depth, the exact numerator count, the normalized alignment formula, and its
real limit.
-/

namespace NField.Alignment

/-- The paper's aligned predicate at synchronized position `j`. -/
def synchronizedAlignedAtPosition (b p u k j : ℕ) : Prop :=
  synchronizedAligned b p (b ^ j * u) k

/-- For a digit-partitioning prime, one synchronized position selects only residues 0 and 1. -/
theorem synchronizedAligned_iff_of_digitPartitioning {b p u k : ℕ}
    (hp : Nat.Prime p) (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u) :
    synchronizedAligned b p u k ↔ k % p = 0 ∨ k % p = 1 := by
  constructor
  · intro h
    rcases h with hzero | hdigit
    · exact Or.inl hzero
    · by_cases hkzero : k % p = 0
      · exact Or.inl hkzero
      · right
        have hunz : u % p ≠ 0 := by
          intro hz
          have hpu : p ∣ u := (Nat.dvd_iff_mod_eq_zero).2 hz
          exact (hp.coprime_iff_not_dvd.mp hu) hpu
        have hkunz : (k * u) % p ≠ 0 := by
          intro hz
          have hdvd : p ∣ k * u := (Nat.dvd_iff_mod_eq_zero).2 hz
          have hpk : p ∣ k := hu.dvd_of_dvd_mul_right hdvd
          exact hkzero ((Nat.dvd_iff_mod_eq_zero).1 hpk)
        have hres : (k * u) % p = u % p :=
          hdp (Nat.pos_of_ne_zero hkunz) (Nat.mod_lt _ hp.pos)
            (Nat.pos_of_ne_zero hunz) (Nat.mod_lt _ hp.pos) hdigit
        have hmul : k * u ≡ 1 * u [MOD p] := by
          simpa [Nat.ModEq] using hres
        have hcancel := Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one hmul
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hcancel
  · intro h
    rcases h with hzero | hone
    · exact Or.inl hzero
    · right
      have hres : (k * u) % p = u % p := by
        calc
          (k * u) % p = ((k % p) * (u % p)) % p := by simp [Nat.mul_mod]
          _ = u % p := by simp [hone]
      exact congrArg (NField.CollisionDefinition.digitBin b p) hres

/-- The residue classification holds at every position on the common clock. -/
theorem synchronizedAlignedAtPosition_iff {b p u k j : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) :
    synchronizedAlignedAtPosition b p u k j ↔
      k % p = 0 ∨ k % p = 1 := by
  apply synchronizedAligned_iff_of_digitPartitioning hp hdp
  exact (prime_coprime_base_pow hp hpb).mul_right hu

/-- A numerator agrees throughout a positive synchronized window. -/
def fullySynchronizedAligned (b p u k length : ℕ) : Prop :=
  ∀ j < length, synchronizedAlignedAtPosition b p u k j

/-- Agreement throughout any positive window is exactly the same two-class condition. -/
theorem fullySynchronizedAligned_iff {b p u k length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) (hlength : 0 < length) :
    fullySynchronizedAligned b p u k length ↔
      k % p = 0 ∨ k % p = 1 := by
  constructor
  · intro h
    exact (synchronizedAlignedAtPosition_iff hp hpb hdp hu).mp (h 0 hlength)
  · intro h j hj
    exact (synchronizedAlignedAtPosition_iff hp hpb hdp hu).mpr h

/-- At a valid clearing depth, the result depends only on the numerator modulo `p`. -/
theorem fullySynchronizedAligned_at_clearing_iff {b p m D k length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hm : m ∣ b ^ D) (hlength : 0 < length) :
    fullySynchronizedAligned b p (clearingCofactor b m D) k length ↔
      k % p = 0 ∨ k % p = 1 := by
  exact fullySynchronizedAligned_iff hp hpb hdp
    (prime_coprime_clearingCofactor hp hpb hm) hlength

/-- Changing between two valid clearing depths cannot change the synchronized result. -/
theorem fullySynchronizedAligned_independent_of_clearing_depth
    {b p m D E k length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E)
    (hlength : 0 < length) :
    fullySynchronizedAligned b p (clearingCofactor b m D) k length ↔
      fullySynchronizedAligned b p (clearingCofactor b m E) k length := by
  rw [fullySynchronizedAligned_at_clearing_iff hp hpb hdp hD hlength,
    fullySynchronizedAligned_at_clearing_iff hp hpb hdp hE hlength]

/-- The number of fully aligned positive numerators below `p*m`. -/
noncomputable def synchronizedFieldAlignedCount
    (b p m u length : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range (p * m)).filter
      (fun k => 0 < k ∧ fullySynchronizedAligned b p u k length)).card

/-- In `m` complete residue blocks, the positive 0 and 1 classes contain `2*m-1` terms. -/
theorem positive_zero_or_one_residue_count {p m : ℕ}
    (hp : 1 < p) (hm : 1 ≤ m) :
    Nat.count (fun k => 0 < k ∧ (k % p = 0 ∨ k % p = 1)) (p * m) =
      2 * m - 1 := by
  let R := Finset.range (p * m)
  let A := R.filter (fun k => k % p = 0)
  let B := R.filter (fun k => k % p = 1)
  have hsplit :
      R.filter (fun k => 0 < k ∧ (k % p = 0 ∨ k % p = 1)) =
        A.erase 0 ∪ B := by
    ext k
    simp only [R, A, B, Finset.mem_filter, Finset.mem_range,
      Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨hkbound, hkpos, hkzero | hkone⟩
      · exact Or.inl ⟨by omega, hkbound, hkzero⟩
      · exact Or.inr ⟨hkbound, hkone⟩
    · rintro (⟨hkne, hkbound, hkzero⟩ | ⟨hkbound, hkone⟩)
      · exact ⟨hkbound, Nat.pos_of_ne_zero hkne, Or.inl hkzero⟩
      · have hkpos : 0 < k := by
          by_contra hknot
          have hk0 : k = 0 := by omega
          subst k
          simp at hkone
        exact ⟨hkbound, hkpos, Or.inr hkone⟩
  have hA0 : 0 ∈ A := by
    have hpm : 0 < p * m := Nat.mul_pos (by omega) (by omega)
    simp [A, R, hpm]
  have hdisjoint : Disjoint (A.erase 0) B := by
    rw [Finset.disjoint_left]
    intro k hkA hkB
    have hkA' : k ∈ A := (Finset.mem_erase.mp hkA).2
    have hkzero : k % p = 0 := (Finset.mem_filter.mp hkA').2
    have hkone : k % p = 1 := (Finset.mem_filter.mp hkB).2
    omega
  have hAcard : A.card = m := by
    change ((Finset.range (p * m)).filter (fun k => k % p = 0)).card = m
    rw [← Nat.count_eq_card_filter_range]
    simpa [residueCount] using
      (residueCount_eq (p := p) (r := 0) (m := m) (by omega))
  have hBcard : B.card = m := by
    change ((Finset.range (p * m)).filter (fun k => k % p = 1)).card = m
    rw [← Nat.count_eq_card_filter_range]
    simpa [residueCount] using
      (residueCount_eq (p := p) (r := 1) (m := m) hp)
  rw [Nat.count_eq_card_filter_range, show Finset.range (p * m) = R by rfl,
    hsplit, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_erase_of_mem hA0, hAcard, hBcard]
  omega

/-- Exactly `2*m-1` positive numerators align throughout the synchronized window. -/
theorem synchronizedFieldAlignedCount_eq {b p m u length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) (hm : 1 ≤ m) (hlength : 0 < length) :
    synchronizedFieldAlignedCount b p m u length = 2 * m - 1 := by
  classical
  unfold synchronizedFieldAlignedCount
  rw [show (Finset.range (p * m)).filter
      (fun k => 0 < k ∧ fullySynchronizedAligned b p u k length) =
      (Finset.range (p * m)).filter
        (fun k => 0 < k ∧ (k % p = 0 ∨ k % p = 1)) by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range,
      fullySynchronizedAligned_iff hp hpb hdp hu hlength]]
  rw [← Nat.count_eq_card_filter_range]
  exact positive_zero_or_one_residue_count hp.one_lt hm

/-- The normalized exact alignment on the synchronized clock. -/
noncomputable def fullySynchronizedAlignment
    (b p m u length : ℕ) : ℚ :=
  (synchronizedFieldAlignedCount b p m u length : ℚ) /
    (p * m - 1 : ℕ)

/-- The exact alignment formula for digit-partitioning primes. -/
theorem fullySynchronizedAlignment_eq {b p m u length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) (hm : 1 ≤ m) (hlength : 0 < length) :
    fullySynchronizedAlignment b p m u length =
      (2 * m - 1 : ℕ) / (p * m - 1 : ℕ) := by
  rw [fullySynchronizedAlignment,
    synchronizedFieldAlignedCount_eq hp hpb hdp hu hm hlength]

/-- The number of synchronized positions that match for one numerator. -/
noncomputable def synchronizedNumeratorMatchCount
    (b p u k length : ℕ) : ℕ := by
  classical
  exact ((Finset.range length).filter
    (fun j => synchronizedAlignedAtPosition b p u k j)).card

/--
For a digit-partitioning prime, a numerator matches at every synchronized
position or at none of them.
-/
theorem synchronizedNumeratorMatchCount_eq {b p u k length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) :
    synchronizedNumeratorMatchCount b p u k length =
      if k % p = 0 ∨ k % p = 1 then length else 0 := by
  classical
  unfold synchronizedNumeratorMatchCount
  by_cases hk : k % p = 0 ∨ k % p = 1
  · simp [synchronizedAlignedAtPosition_iff hp hpb hdp hu, hk]
  · simp [synchronizedAlignedAtPosition_iff hp hpb hdp hu, hk]

/-- Total synchronized digit matches over numerators `1, ..., p*m-1`. -/
noncomputable def synchronizedFieldMatchCount
    (b p m u length : ℕ) : ℕ := by
  classical
  exact ((Finset.range (p * m)).filter (fun k => 0 < k)).sum
    (fun k => synchronizedNumeratorMatchCount b p u k length)

/-- The field contains exactly `(2*m-1)*length` synchronized digit matches. -/
theorem synchronizedFieldMatchCount_eq {b p m u length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) (hm : 1 ≤ m) :
    synchronizedFieldMatchCount b p m u length = (2 * m - 1) * length := by
  classical
  unfold synchronizedFieldMatchCount
  simp_rw [synchronizedNumeratorMatchCount_eq hp hpb hdp hu]
  rw [← Finset.sum_filter]
  rw [show ((Finset.range (p * m)).filter (fun k => 0 < k)).filter
      (fun k => k % p = 0 ∨ k % p = 1) =
      (Finset.range (p * m)).filter
        (fun k => 0 < k ∧ (k % p = 0 ∨ k % p = 1)) by
    ext k
    simp [and_assoc]]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Nat.count_eq_card_filter_range]
  rw [positive_zero_or_one_residue_count hp.one_lt hm]
  simp

/--
The manuscript's mean match proportion.  The numerator is the total number of
matching synchronized positions and the denominator is the number of compared
fractions times the positive window length.
-/
noncomputable def synchronizedRepetendAlignment
    (b p m u length : ℕ) : ℚ :=
  (synchronizedFieldMatchCount b p m u length : ℚ) /
    ((p * m - 1) * length : ℕ)

/-- The exact repetend-alignment formula, proved from the position-wise mean. -/
theorem synchronizedRepetendAlignment_eq {b p m u length : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hu : Nat.Coprime p u) (hm : 1 ≤ m) (hlength : 0 < length) :
    synchronizedRepetendAlignment b p m u length =
      (2 * m - 1 : ℕ) / (p * m - 1 : ℕ) := by
  rw [synchronizedRepetendAlignment,
    synchronizedFieldMatchCount_eq hp hpb hdp hu hm]
  have hden : 0 < p * m - 1 := by
    have hpm : 1 < p * m := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    omega
  push_cast
  field_simp

/--
The paper-facing package: a supported denominator supplies a common clearing
depth, and at that depth every positive synchronized window has the claimed
exact alignment.
-/
theorem digitPartitioningAlignment_certificate {b p m length : ℕ}
    (_hb : 2 ≤ b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hle : p ≤ b + 1)
    (hm : 1 ≤ m) (hsupported : Supported b m) (hlength : 0 < length) :
    ∃ D : ℕ, m ∣ b ^ D ∧
      synchronizedRepetendAlignment b p m (clearingCofactor b m D) length =
        (2 * m - 1 : ℕ) / (p * m - 1 : ℕ) := by
  rcases hsupported with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  exact synchronizedRepetendAlignment_eq hp hpb
    (digitPartitioning_of_le hp.pos hpb hle)
    (prime_coprime_clearingCofactor hp hpb hD) hm hlength

/-- The exact formula interpreted over the real numbers. -/
noncomputable def digitPartitioningAlignmentFormulaReal (p m : ℕ) : ℝ :=
  ((2 : ℝ) * m - 1) / ((p : ℝ) * m - 1)

/-- The alignment formula tends to `2/p`, even before restricting to supported `m`. -/
theorem digitPartitioningAlignmentFormulaReal_tendsto {p : ℕ} (hp : 0 < p) :
    Filter.Tendsto (digitPartitioningAlignmentFormulaReal p) Filter.atTop
      (nhds ((2 : ℝ) / p)) := by
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) 2 (d := (p : ℝ)) (by exact_mod_cast hp.ne')) using 1
  funext k
  simp only [digitPartitioningAlignmentFormulaReal, sub_eq_add_neg]
  ring

end NField.Alignment
