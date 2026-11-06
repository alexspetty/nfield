/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TerminalCollisionBoundary
import NField.Alignment.LiftedBoundaryInvisibility
import NField.Alignment.CarrySourceCorollaries

/-! # The terminal mean law for the actual first and last digit indicator -/

noncomputable section
namespace NField.Alignment.TerminalCarrySource
open scoped BigOperators Classical
open CollisionCharacterStructure CarryBoundarySpectra TerminalCollisionBoundary
  PrimitiveOddBoundaryMean PairedBoundary LiftedBoundaryInvisibility

/-- The indicator of equality of the first and last padded base digits. -/
def terminalDigitWeight (p N : ℕ) (x : ZMod (p ^ N)) : ℂ :=
  if x.val / p ^ (N - 1) = x.val % p then 1 else 0

theorem block_digit_div {p P a y c : ℕ} (hp : 0 < p) (hP : 0 < P)
    (hy : y < P) (hc : c < p) :
    (a * (p * P) + p * y + c) / (p * P) = a := by
  have ht : p * y + c < p * P := by nlinarith
  rw [show a * (p * P) + p * y + c = (p * P) * a + (p * y + c) by ring,
    Nat.mul_add_div (mul_pos hp hP), Nat.div_eq_of_lt ht, add_zero]

theorem block_digit_mod {p P a y c : ℕ} (hc : c < p) :
    (a * (p * P) + p * y + c) % p = c := by
  rw [show a * (p * P) + p * y + c = c + p * (a * P + y) by ring]
  simp [Nat.mod_eq_of_lt hc]

theorem terminal_top_power {p N : ℕ} (hN : 2 ≤ N) :
    p ^ (N - 1) = p * p ^ (N - 2) := by
  rw [show N - 1 = (N - 2) + 1 by omega, pow_succ']

theorem terminalCoordinateFacts {p N : ℕ} [NeZero (p ^ N)]
    (hp : 0 < p) (hN : 2 ≤ N) (x : ZMod (p ^ N)) :
    x.val / p ^ (N - 1) < p ∧
    x.val % p ^ (N - 1) / p < p ^ (N - 2) ∧
    x.val = x.val / p ^ (N - 1) * p ^ (N - 1) +
      p * (x.val % p ^ (N - 1) / p) + x.val % p := by
  have hP : 0 < p ^ (N - 1) := pow_pos hp _
  have hbig : p ^ N = p * p ^ (N - 1) := by
    calc
      p ^ N = p ^ ((N - 1) + 1) := by congr 1; omega
      _ = p * p ^ (N - 1) := pow_succ' _ _
  have hd : p ∣ p ^ (N - 1) := by rw [terminal_top_power hN]; exact dvd_mul_right _ _
  constructor
  · rw [Nat.div_lt_iff_lt_mul hP]
    simpa only [hbig] using x.val_lt
  constructor
  · rw [Nat.div_lt_iff_lt_mul hp, mul_comm, ← terminal_top_power hN]
    exact Nat.mod_lt _ hP
  · have h₁ := Nat.div_add_mod x.val (p ^ (N - 1))
    have h₂ := Nat.div_add_mod (x.val % p ^ (N - 1)) p
    rw [Nat.mod_mod_of_dvd _ hd] at h₂
    nlinarith

theorem unitLastDigit_pos {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (u : UnitClass (p ^ N)) : 0 < u.val.val % p := by
  have hcop : u.val.val.Coprime (p ^ N) := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa only [ZMod.natCast_zmod_val] using u.isUnit
  have hcop' : u.val.val.Coprime p :=
    hcop.of_dvd_right (dvd_pow_self p (by omega : N ≠ 0))
  have hn : ¬ p ∣ u.val.val := hp.coprime_iff_not_dvd.mp hcop'.symm
  exact Nat.pos_of_ne_zero (fun h => hn (Nat.dvd_of_mod_eq_zero h))

theorem terminalLeftUnit_exists_iff {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (u : UnitClass (p ^ N)) :
    (∃ i, terminalLeftUnit hp hN i = u) ↔
      u.val.val / p ^ (N - 1) = u.val.val % p := by
  constructor
  · rintro ⟨i, rfl⟩
    change ((terminalLeftNat p N i : ZMod (p ^ N)).val / p ^ (N - 1)) =
      (terminalLeftNat p N i : ZMod (p ^ N)).val % p
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (terminalLeftNat_lt_modulus hp hN i),
      terminalNat_mod_p_left hp hN]
    unfold terminalLeftNat
    rw [terminal_top_power hN]
    exact block_digit_div hp.pos (pow_pos hp.pos _) (terminalY_lt i)
      (terminalC_lt hp.two_le i)
  · intro heq
    obtain ⟨_, hy, hn⟩ := terminalCoordinateFacts hp.pos hN u.val
    have hc0 := unitLastDigit_pos hp hN u
    have hc := Nat.mod_lt u.val.val hp.pos
    let i : TerminalUnitIndex p N :=
      (⟨u.val.val % p - 1, by omega⟩, ⟨u.val.val % p ^ (N - 1) / p, hy⟩)
    have hi : terminalC i = u.val.val % p := by dsimp [terminalC, i]; omega
    refine ⟨i, ?_⟩
    apply Units.ext
    change (terminalLeftNat p N i : ZMod (p ^ N)) = u.val
    have hn' : terminalLeftNat p N i = u.val.val := by
      unfold terminalLeftNat
      rw [hi]
      change u.val.val % p * p ^ (N - 1) +
        p * (u.val.val % p ^ (N - 1) / p) + u.val.val % p = _
      simpa only [heq] using hn.symm
    rw [hn', ZMod.natCast_zmod_val]

theorem terminalRightUnit_exists_iff {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (u : UnitClass (p ^ N)) :
    (∃ i, terminalRightUnit hp hN i = u) ↔
      u.val.val / p ^ (N - 1) = u.val.val % p - 1 := by
  constructor
  · rintro ⟨i, rfl⟩
    change ((terminalRightNat p N i : ZMod (p ^ N)).val / p ^ (N - 1)) =
      (terminalRightNat p N i : ZMod (p ^ N)).val % p - 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (terminalRightNat_lt_modulus hp hN i),
      terminalNat_mod_p_right hp hN]
    unfold terminalRightNat
    rw [terminal_top_power hN]
    exact block_digit_div hp.pos (pow_pos hp.pos _) (terminalY_lt i)
      (terminalC_lt hp.two_le i)
  · intro heq
    obtain ⟨_, hy, hn⟩ := terminalCoordinateFacts hp.pos hN u.val
    have hc0 := unitLastDigit_pos hp hN u
    have hc := Nat.mod_lt u.val.val hp.pos
    let i : TerminalUnitIndex p N :=
      (⟨u.val.val % p - 1, by omega⟩, ⟨u.val.val % p ^ (N - 1) / p, hy⟩)
    have hi : terminalC i = u.val.val % p := by dsimp [terminalC, i]; omega
    refine ⟨i, ?_⟩
    apply Units.ext
    change (terminalRightNat p N i : ZMod (p ^ N)) = u.val
    have hn' : terminalRightNat p N i = u.val.val := by
      unfold terminalRightNat
      rw [hi]
      change (u.val.val % p - 1) * p ^ (N - 1) +
        p * (u.val.val % p ^ (N - 1) / p) + u.val.val % p = _
      simpa only [heq] using hn.symm
    rw [hn', ZMod.natCast_zmod_val]

theorem terminalDigitWeight_pred_unit {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (u : UnitClass (p ^ N)) :
    terminalDigitWeight p N (u.val - 1) =
      if u.val.val / p ^ (N - 1) = u.val.val % p - 1 then 1 else 0 := by
  have hmod : 2 ≤ p ^ N := hp.two_le.trans (Nat.le_pow (by omega : 0 < N))
  letI : Fact (1 < p ^ N) := ⟨by omega⟩
  have hc0 := unitLastDigit_pos hp hN u
  have hc := Nat.mod_lt u.val.val hp.pos
  obtain ⟨_, hy, hn⟩ := terminalCoordinateFacts hp.pos hN u.val
  have hn0 : 0 < u.val.val := by omega
  have hpred : (u.val - 1).val = u.val.val - 1 := by
    rw [ZMod.val_sub (by rw [ZMod.val_one]; exact hn0), ZMod.val_one]
  have hdecomp : u.val.val - 1 =
      u.val.val / p ^ (N - 1) * (p * p ^ (N - 2)) +
        p * (u.val.val % p ^ (N - 1) / p) + (u.val.val % p - 1) := by
    rw [← terminal_top_power hN]
    omega
  unfold terminalDigitWeight
  rw [hpred, hdecomp]
  rw [terminal_top_power hN] at hy
  rw [terminal_top_power hN,
    block_digit_div hp.pos (pow_pos hp.pos _) hy (by omega),
    block_digit_mod (by omega)]

/-- Title: `The actual terminal digit indicator has the proved unit boundary`. -/
theorem terminal_digit_unit_boundary {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (u : UnitClass (p ^ N)) :
    signedBoundary (terminalDigitWeight p N) u.val = terminalUnitBoundary hp hN u := by
  change terminalDigitWeight p N (u.val - 1) - terminalDigitWeight p N u.val =
    pairedBoundary (terminalLeftUnit hp hN) (terminalRightUnit hp hN) u
  rw [terminalDigitWeight_pred_unit hp hN]
  unfold pairedBoundary
  rw [imageIndicator_eq_one_or_zero _ (terminalRightUnit_injective hp hN),
    imageIndicator_eq_one_or_zero _ (terminalLeftUnit_injective hp hN)]
  simp only [terminalRightUnit_exists_iff hp hN, terminalLeftUnit_exists_iff hp hN,
    terminalDigitWeight]

/-- Title: `Terminal digit flux equals the explicit endpoint flux`. -/
theorem terminal_digit_flux {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) (χ : Character (p ^ N)) :
    cellBoundaryFlux (terminalDigitWeight p N) χ = boundaryFlux (terminalUnitBoundary hp hN) χ := by
  rw [cellBoundaryFlux_eq_boundary_pairing, sum_character_pairing_eq_units]
  simp_rw [terminal_digit_unit_boundary hp hN]
  rfl

/-- Title: `Boundary mean law for actual first and last digit agreement`. -/
theorem actual_terminal_collision_mean {p N : ℕ} [NeZero (p ^ N)]
    [NeZero (p ^ (N - 1))] (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N) :
    (∑ χ : Character (p ^ N) with χ.IsPrimitive ∧ χ.Odd,
      ‖cellBoundaryFlux (terminalDigitWeight p N) χ‖ ^ 2) /
        primitiveOddCharacterCount (p ^ N) = 2 * terminalFormalBoundarySize p N := by
  classical
  simp_rw [terminal_digit_flux hp hN]
  exact terminalUnitBoundary_meanLaw hp hpodd hN

end NField.Alignment.TerminalCarrySource
