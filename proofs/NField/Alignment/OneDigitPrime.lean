/-
Author: Alexander S. Petty
-/

import NField.Alignment.DigitPartitioning

/-!
The synchronized one-digit alignment theorem from
"Three and the Golden Ratio."

The important bridge is `synchronizedAligned_iff_residue_zero_or_one`: the
long-division digit comparison is proved equivalent to the two residue classes
counted in the paper.  The clearing-depth theorem then shows that this result
does not depend on which common depth is chosen.
-/

namespace NField.Alignment

open NField.CollisionDefinition

/-- When `b ≡ 1 (mod p)`, the digit produced by a residue is a fixed scale times it. -/
theorem digitBin_eq_scale {b p r : ℕ} (hp : 0 < p) (hr : r < p)
    (hmod : b % p = 1) :
    digitBin b p r = (b / p) * r := by
  have hb0 := Nat.mod_add_div b p
  have hb : b = 1 + p * (b / p) := by omega
  unfold digitBin
  calc
    (b * r) / p = ((1 + p * (b / p)) * r) / p :=
      congrArg (fun x => (x * r) / p) hb
    _ = (r + p * ((b / p) * r)) / p := by congr 1; ring
    _ = r / p + (b / p) * r := Nat.add_mul_div_left r ((b / p) * r) hp
    _ = (b / p) * r := by rw [Nat.div_eq_of_lt hr, zero_add]

/-- Distinct residue representatives produce distinct one-digit repetends. -/
theorem digitBin_injective_on_residues {b p r s : ℕ} (hp : 0 < p)
    (hb : 1 < b) (hr : r < p) (hs : s < p) (hmod : b % p = 1)
    (h : digitBin b p r = digitBin b p s) : r = s := by
  rw [digitBin_eq_scale hp hr hmod, digitBin_eq_scale hp hs hmod] at h
  have hb0 := Nat.mod_add_div b p
  have hbp : 0 < b / p := by
    have hprod : 0 < p * (b / p) := by omega
    exact Nat.pos_of_mul_pos_left hprod
  exact Nat.eq_of_mul_eq_mul_left hbp h

/-- When the base is one modulo the prime, every later digit is the initial
digit. This is the exact one-digit-period statement. -/
theorem digitAt_eq_initial_of_mod_one {b p r j : ℕ}
    (hp : 1 < p) (hmod : b % p = 1) :
    digitAt b p r j = digitBin b p (r % p) := by
  unfold digitAt
  have hpow : b ^ j % p = 1 := by
    rw [Nat.pow_mod, hmod]
    simp [Nat.mod_eq_of_lt hp]
  rw [Nat.mul_mod, hpow]
  simp

/--
The synchronized digit test is exactly the union of the terminating residue
class zero and the reference residue class one.
-/
theorem synchronizedAligned_iff_residue_zero_or_one {b p u k : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b) (hmod : b % p = 1)
    (hu : Nat.Coprime p u) :
    synchronizedAligned b p u k ↔ k % p = 0 ∨ k % p = 1 := by
  constructor
  · intro h
    rcases h with hzero | hdigit
    · exact Or.inl hzero
    · right
      have hku : (k * u) % p < p := Nat.mod_lt _ hp.pos
      have hu' : u % p < p := Nat.mod_lt _ hp.pos
      have hres : (k * u) % p = u % p :=
        digitBin_injective_on_residues hp.pos (by omega) hku hu' hmod hdigit
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
      exact congrArg (digitBin b p) hres

/-- The one-digit synchronized predicate is exactly the manuscript's literal
tail condition: termination by convention, or equality at every later digit. -/
theorem synchronizedAligned_iff_terminates_or_all_digits {b p u k : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b) (hmod : b % p = 1)
    (hu : Nat.Coprime p u) :
    synchronizedAligned b p u k ↔
      k % p = 0 ∨
        ∀ j : ℕ,
          digitAt b p ((k * u) % p) j = digitAt b p (u % p) j := by
  rw [synchronizedAligned_iff_residue_zero_or_one hp hb hmod hu]
  constructor
  · rintro (hzero | hone)
    · exact Or.inl hzero
    · right
      intro j
      rw [digitAt_eq_initial_of_mod_one hp.one_lt hmod,
        digitAt_eq_initial_of_mod_one hp.one_lt hmod]
      congr 1
      simp [Nat.mul_mod, hone]
  · rintro (hzero | hall)
    · exact Or.inl hzero
    · right
      have hzeroDigit := hall 0
      simp only [digitAt, pow_zero, one_mul] at hzeroDigit
      have hku : (k * u) % p < p := Nat.mod_lt _ hp.pos
      have hu' : u % p < p := Nat.mod_lt _ hp.pos
      rw [Nat.mod_eq_of_lt hku, Nat.mod_eq_of_lt hu'] at hzeroDigit
      have hres : (k * u) % p = u % p :=
        digitBin_injective_on_residues hp.pos (by omega) hku hu' hmod hzeroDigit
      have hmul : k * u ≡ 1 * u [MOD p] := by
        simpa [Nat.ModEq] using hres
      have hcancel := Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one hmul
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hcancel

/-- The classification at a valid supported-denominator clearing depth. -/
theorem synchronizedAligned_at_clearing_iff {b p m D k : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b) (hpb : ¬p ∣ b)
    (hmod : b % p = 1) (hm : m ∣ b ^ D) :
    synchronizedAligned b p (clearingCofactor b m D) k ↔
      k % p = 0 ∨ k % p = 1 := by
  exact synchronizedAligned_iff_residue_zero_or_one hp hb hmod
    (prime_coprime_clearingCofactor hp hpb hm)

/-- Choosing a different common clearing depth does not change alignment. -/
theorem synchronizedAligned_independent_of_clearing_depth {b p m D E k : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b) (hpb : ¬p ∣ b)
    (hmod : b % p = 1) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    synchronizedAligned b p (clearingCofactor b m D) k ↔
      synchronizedAligned b p (clearingCofactor b m E) k := by
  rw [synchronizedAligned_at_clearing_iff hp hb hpb hmod hD,
    synchronizedAligned_at_clearing_iff hp hb hpb hmod hE]

/-- The exact normalized alignment formula after the two classes are counted. -/
theorem oneDigitAlignment_eq {p m : ℕ} (hp : Nat.Prime p) :
    oneDigitAlignment p m =
      ((2 * m - 1 : ℕ) : ℚ) / ((p * m - 1 : ℕ) : ℚ) := by
  simp only [oneDigitAlignment, alignedNumeratorCount_eq hp.one_lt]

/--
A single theorem packages the common-depth witness, the residue classification,
and the exact alignment formula under the manuscript's hypotheses.
-/
theorem generalPrimeAlignment_certificate {b p m : ℕ}
    (hp : Nat.Prime p) (hb : 2 ≤ b) (hpb : ¬p ∣ b)
    (hmod : b % p = 1) (hm : Supported b m) :
    ∃ D : ℕ,
      m ∣ b ^ D ∧
      (∀ k : ℕ,
        synchronizedAligned b p (clearingCofactor b m D) k ↔
          k % p = 0 ∨ k % p = 1) ∧
      oneDigitAlignment p m =
        ((2 * m - 1 : ℕ) : ℚ) / ((p * m - 1 : ℕ) : ℚ) := by
  rcases hm with ⟨D, hD⟩
  refine ⟨D, hD, ?_, oneDigitAlignment_eq hp⟩
  intro k
  exact synchronizedAligned_at_clearing_iff hp hb hpb hmod hD

/-- The two nonzero decimal residues modulo three produce digits three and six. -/
theorem base_ten_mod_three_digits :
    digitBin 10 3 1 = 3 ∧ digitBin 10 3 2 = 6 := by
  norm_num [digitBin]

/-- The paper's three-class result, specialized to base ten and rough prime three. -/
theorem base_ten_three_class_certificate {m : ℕ} (hm : Supported 10 m) :
    ∃ D : ℕ,
      m ∣ 10 ^ D ∧
      ∀ k : ℕ,
        synchronizedAligned 10 3 (clearingCofactor 10 m D) k ↔
          k % 3 = 0 ∨ k % 3 = 1 := by
  rcases hm with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  intro k
  exact synchronizedAligned_at_clearing_iff Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) hD

/-- The exact base-10 prime-three alignment formula. -/
theorem base_ten_prime_three_alignment (m : ℕ) :
    oneDigitAlignment 3 m =
      ((2 * m - 1 : ℕ) : ℚ) / ((3 * m - 1 : ℕ) : ℚ) := by
  exact oneDigitAlignment_eq Nat.prime_three

end NField.Alignment
