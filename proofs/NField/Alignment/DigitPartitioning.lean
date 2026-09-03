/-
Author: Alexander S. Petty
-/

import Mathlib
import NField.Alignment.SupportedDenominators

/-!
# Digit-Partitioning Primes and the Alignment Formula

This file checks the arithmetic boundary in
`papers/digit_partition_primes.tex`.  It proves that the long-division digit
map is injective on the nonzero residues exactly when `p ≤ b + 1`, and
that this is equivalent to separating every pair of nonzero residues at every
synchronized position.
-/

namespace NField.Alignment

open NField.CollisionDefinition

/-- At the endpoint `p = b + 1`, the digit attached to `r` is exactly `r - 1`. -/
theorem boundary_digit {b p r : ℕ} (hp : p = b + 1)
    (hr0 : 0 < r) (hr : r < p) :
    digitBin b p r = r - 1 := by
  unfold digitBin
  apply Nat.div_eq_of_lt_le
  · subst p
    have hrle : r ≤ b := by omega
    have hrone : 1 ≤ r := by omega
    calc
      (r - 1) * (b + 1) = b * (r - 1) + (r - 1) := by ring
      _ ≤ b * (r - 1) + b := Nat.add_le_add_left (by omega) _
      _ = b * ((r - 1) + 1) := by ring
      _ = b * r := by rw [Nat.sub_add_cancel hrone]
  · subst p
    have hbr : b * r < (b + 1) * r :=
      Nat.mul_lt_mul_of_pos_right (by omega) hr0
    have hrone : 1 ≤ r := by omega
    calc
      b * r < (b + 1) * r := hbr
      _ = ((r - 1) + 1) * (b + 1) := by
        rw [Nat.sub_add_cancel hrone]
        ring

/-- Above the endpoint, increasing a residue strictly increases its digit. -/
theorem above_digit_strict {b p r s : ℕ} (hp : 0 < p) (hbp : p < b)
    (hrs : r < s) : digitBin b p r < digitBin b p s := by
  unfold digitBin
  have hrs' : r + 1 ≤ s := by omega
  have hmul : b * (r + 1) ≤ b * s := Nat.mul_le_mul_left b hrs'
  have hgap : b * r + p < b * s := by
    calc
      b * r + p < b * r + b := Nat.add_lt_add_left hbp (b * r)
      _ = b * (r + 1) := by ring
      _ ≤ b * s := hmul
  have hrmod : (b * r) % p < p := Nat.mod_lt _ hp
  have hsmod : (b * s) % p < p := Nat.mod_lt _ hp
  have hrdecomp := Nat.mod_add_div (b * r) p
  have hsdecomp := Nat.mod_add_div (b * s) p
  have hbrs : b * r < b * s := by omega
  have hle : (b * r) / p ≤ (b * s) / p :=
    Nat.div_le_div_right (Nat.le_of_lt hbrs)
  by_contra hnot
  have hge : (b * s) / p ≤ (b * r) / p := by omega
  have heq : (b * r) / p = (b * s) / p := Nat.le_antisymm hle hge
  rw [← heq] at hsdecomp
  omega

/-- The digit map is one-to-one on the nonzero residue classes modulo `p`. -/
def DigitPartitioning (b p : ℕ) : Prop :=
  ∀ ⦃r s : ℕ⦄, 0 < r → r < p → 0 < s → s < p →
    digitBin b p r = digitBin b p s → r = s

/-- Every digit produced from a residue below `p` is below the base. -/
theorem digitBin_lt_base {b p r : ℕ} (hb : 0 < b) (hp : 0 < p)
    (hr : r < p) : digitBin b p r < b := by
  unfold digitBin
  rw [Nat.div_lt_iff_lt_mul hp]
  exact Nat.mul_lt_mul_of_pos_left hr hb

/-- The paper's forward boundary: `p ≤ b + 1` forces digit partitioning. -/
theorem digitPartitioning_of_le {b p : ℕ} (hp : 0 < p) (hpb : ¬p ∣ b)
    (hle : p ≤ b + 1) : DigitPartitioning b p := by
  intro r s hr0 hr hs0 hs hdigit
  by_cases hboundary : p = b + 1
  · rw [boundary_digit hboundary hr0 hr,
        boundary_digit hboundary hs0 hs] at hdigit
    omega
  · have hpb' : p < b := by
      have hpne : p ≠ b := by
        intro heq
        apply hpb
        rw [heq]
      omega
    rcases Nat.lt_trichotomy r s with hrs | hrs | hrs
    · have hlt := above_digit_strict hp hpb' hrs
      omega
    · exact hrs
    · have hlt := above_digit_strict hp hpb' hrs
      omega

/-- Injectivity into `b` digits forces `p - 1 ≤ b`. -/
theorem digitPartitioning_le {b p : ℕ} (hb : 0 < b) (hp : 1 < p)
    (hdp : DigitPartitioning b p) : p ≤ b + 1 := by
  let f : Fin (p - 1) → Fin b := fun x =>
    ⟨digitBin b p (x.1 + 1), digitBin_lt_base hb (by omega) (by omega)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have hadd : x.1 + 1 = y.1 + 1 :=
      hdp (by omega) (by omega) (by omega) (by omega)
        (congrArg Fin.val hxy)
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

/-- Exact characterization of the digit-partitioning primes in a base. -/
theorem digitPartitioning_iff {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) : DigitPartitioning b p ↔ p ≤ b + 1 := by
  constructor
  · exact digitPartitioning_le hb hp.one_lt
  · exact digitPartitioning_of_le hp.pos hpb

/-- The digit at synchronized position `j` in the expansion starting at residue `k`. -/
def digitAt (b p k j : ℕ) : ℕ :=
  digitBin b p ((b ^ j * k) % p)

/-- Every pair of distinct nonzero residue classes has different digits at every position. -/
def PositionSeparated (b p : ℕ) : Prop :=
  ∀ ⦃r s : ℕ⦄, 0 < r → r < p → 0 < s → s < p → r ≠ s →
    ∀ j : ℕ, digitAt b p r j ≠ digitAt b p s j

/-- Multiplication by a base power preserves distinct residues and hence distinct digits. -/
theorem digitAt_separated {b p r s j : ℕ} (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hdp : DigitPartitioning b p)
    (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p)
    (hrs : r ≠ s) : digitAt b p r j ≠ digitAt b p s j := by
  intro hdigit
  have hcop : Nat.Coprime p (b ^ j) := prime_coprime_base_pow hp hpb
  have hrnz : (b ^ j * r) % p ≠ 0 := by
    intro hz
    have hdvd : p ∣ b ^ j * r := (Nat.dvd_iff_mod_eq_zero).2 hz
    have hpr : p ∣ r := hcop.dvd_of_dvd_mul_left hdvd
    have hrmod : r % p = 0 := (Nat.dvd_iff_mod_eq_zero).1 hpr
    rw [Nat.mod_eq_of_lt hr] at hrmod
    omega
  have hsnz : (b ^ j * s) % p ≠ 0 := by
    intro hz
    have hdvd : p ∣ b ^ j * s := (Nat.dvd_iff_mod_eq_zero).2 hz
    have hps : p ∣ s := hcop.dvd_of_dvd_mul_left hdvd
    have hsmod : s % p = 0 := (Nat.dvd_iff_mod_eq_zero).1 hps
    rw [Nat.mod_eq_of_lt hs] at hsmod
    omega
  have hres : (b ^ j * r) % p = (b ^ j * s) % p :=
    hdp (Nat.pos_of_ne_zero hrnz) (Nat.mod_lt _ hp.pos)
      (Nat.pos_of_ne_zero hsnz) (Nat.mod_lt _ hp.pos) hdigit
  have hmul : b ^ j * r ≡ b ^ j * s [MOD p] := by
    simpa [Nat.ModEq] using hres
  have hcancel := Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hmul
  have hrsmod : r % p = s % p := by simpa [Nat.ModEq] using hcancel
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hrsmod
  exact hrs hrsmod

/-- The paper's positional definition is equivalent to injectivity of the digit map. -/
theorem positionSeparated_iff_digitPartitioning {b p : ℕ} (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) : PositionSeparated b p ↔ DigitPartitioning b p := by
  constructor
  · intro hsep r s hr0 hr hs0 hs hdigit
    by_contra hne
    have h := hsep hr0 hr hs0 hs hne 0
    simp [digitAt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at h
    exact h hdigit
  · intro hdp r s hr0 hr hs0 hs hrs j
    exact digitAt_separated hp hpb hdp hr0 hr hs0 hs hrs

end NField.Alignment
