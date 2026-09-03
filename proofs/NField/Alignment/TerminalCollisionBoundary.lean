/-
Author: Alexander S. Petty
-/

import NField.Alignment.PairedBoundary
import NField.Alignment.PrimitiveOddBoundaryMean

namespace NField.Alignment.TerminalCollisionBoundary

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PairedBoundary
open NField.Alignment.PrimitiveOddBoundaryMean

abbrev TerminalUnitIndex (p N : ℕ) :=
  Fin (p - 1) × Fin (p ^ (N - 2))

abbrev TerminalCellIndex (p N : ℕ) :=
  Fin p × Fin (p ^ (N - 2))

def terminalCellNat (p N : ℕ) (i : TerminalCellIndex p N) : ℕ :=
  i.1.val * p ^ (N - 1) + p * i.2.val + i.1.val

theorem terminalCellCount
    {p N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (TerminalCellIndex p N) = p ^ (N - 1) := by
  simp only [TerminalCellIndex, Fintype.card_prod, Fintype.card_fin]
  have he : N - 1 = (N - 2) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem terminalCellNat_lt_modulus
    {p N : ℕ} (hN : 2 ≤ N)
    (i : TerminalCellIndex p N) :
    terminalCellNat p N i < p ^ N := by
  let P := p ^ (N - 2)
  have ha : i.1.val < p := i.1.isLt
  have hy : i.2.val < P := i.2.isLt
  have htail : i.1.val + p * i.2.val < p * P := by
    calc
      i.1.val + p * i.2.val < p * (i.2.val + 1) := by
        nlinarith
      _ ≤ p * P := Nat.mul_le_mul_left p (by omega)
  have hlead : (i.1.val + 1) * (p * P) ≤ p * (p * P) :=
    Nat.mul_le_mul_right (p * P) (by omega)
  have hpow : p ^ N = p * p * P := by
    calc
      p ^ N = p ^ ((N - 2) + 2) := by congr 1; omega
      _ = p ^ (N - 2) * p ^ 2 := by rw [pow_add]
      _ = p * p * P := by simp only [P]; ring
  unfold terminalCellNat
  have he : N - 1 = (N - 2) + 1 := by omega
  rw [he, pow_succ, hpow]
  calc
    i.1.val * (P * p) + p * i.2.val + i.1.val =
        i.1.val * (p * P) + (i.1.val + p * i.2.val) := by ring
    _ <
        i.1.val * (p * P) + p * P := Nat.add_lt_add_left htail _
    _ = (i.1.val + 1) * (p * P) := by ring
    _ ≤ p * (p * P) := hlead
    _ = p * p * P := by ring

theorem terminalCellNat_mod_p
    {p N : ℕ} (hN : 2 ≤ N)
    (i : TerminalCellIndex p N) :
    terminalCellNat p N i % p = i.1.val := by
  unfold terminalCellNat
  have he : N - 1 = (N - 2) + 1 := by omega
  rw [he, pow_succ]
  rw [show i.1.val * (p ^ (N - 2) * p) + p * i.2.val + i.1.val =
      i.1.val + p * (i.1.val * p ^ (N - 2) + i.2.val) by ring]
  simp [Nat.mod_eq_of_lt i.1.isLt]

theorem terminalCellNat_injective
    {p N : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    Function.Injective (terminalCellNat p N) := by
  intro i j hij
  have ha : i.1.val = j.1.val := by
    calc
      i.1.val = terminalCellNat p N i % p :=
        (terminalCellNat_mod_p hN i).symm
      _ = terminalCellNat p N j % p := by rw [hij]
      _ = j.1.val := terminalCellNat_mod_p hN j
  apply Prod.ext
  · exact Fin.ext ha
  · apply Fin.ext
    unfold terminalCellNat at hij
    rw [ha] at hij
    have hmul : p * i.2.val = p * j.2.val := by omega
    exact Nat.mul_left_cancel hp hmul

noncomputable def terminalCollisionSupport
    (p N : ℕ) : Finset ℕ :=
  Finset.univ.image (terminalCellNat p N)

theorem terminalCollisionSupport_card
    {p N : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    (terminalCollisionSupport p N).card = p ^ (N - 1) := by
  unfold terminalCollisionSupport
  rw [Finset.card_image_of_injective _ (terminalCellNat_injective hp hN)]
  exact terminalCellCount hN

def terminalC {p N : ℕ} (i : TerminalUnitIndex p N) : ℕ :=
  i.1.val + 1

def terminalY {p N : ℕ} (i : TerminalUnitIndex p N) : ℕ :=
  i.2.val

def terminalLeftNat (p N : ℕ) (i : TerminalUnitIndex p N) : ℕ :=
  terminalC i * p ^ (N - 1) + p * terminalY i + terminalC i

def terminalRightNat (p N : ℕ) (i : TerminalUnitIndex p N) : ℕ :=
  (terminalC i - 1) * p ^ (N - 1) + p * terminalY i + terminalC i

theorem terminalC_pos {p N : ℕ} (i : TerminalUnitIndex p N) :
    0 < terminalC i := by
  unfold terminalC
  omega

theorem terminalC_lt {p N : ℕ} (hp : 2 ≤ p)
    (i : TerminalUnitIndex p N) : terminalC i < p := by
  unfold terminalC
  have := i.1.isLt
  omega

theorem terminalY_lt {p N : ℕ} (i : TerminalUnitIndex p N) :
    terminalY i < p ^ (N - 2) := i.2.isLt

theorem terminalC_coprime
    {p N : ℕ} (hp : p.Prime) (i : TerminalUnitIndex p N) :
    (terminalC i).Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (terminalC_pos i) (terminalC_lt hp.two_le i)

theorem terminalLeftNat_eq_coarse
    {p N : ℕ} (hN : 2 ≤ N) (i : TerminalUnitIndex p N) :
    terminalLeftNat p N i =
      terminalC i + p * (terminalC i * p ^ (N - 2) + terminalY i) := by
  unfold terminalLeftNat
  have he : N - 1 = (N - 2) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem terminalRightNat_eq_coarse
    {p N : ℕ} (hN : 2 ≤ N) (i : TerminalUnitIndex p N) :
    terminalRightNat p N i =
      terminalC i + p * ((terminalC i - 1) * p ^ (N - 2) + terminalY i) := by
  unfold terminalRightNat
  have he : N - 1 = (N - 2) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem terminalLeftNat_coprime
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    (terminalLeftNat p N i).Coprime (p ^ N) := by
  rw [Nat.coprime_pow_right_iff (by omega)]
  rw [terminalLeftNat_eq_coarse hN]
  rw [Nat.coprime_add_mul_left_left]
  exact terminalC_coprime hp i

theorem terminalRightNat_coprime
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    (terminalRightNat p N i).Coprime (p ^ N) := by
  rw [Nat.coprime_pow_right_iff (by omega)]
  rw [terminalRightNat_eq_coarse hN]
  rw [Nat.coprime_add_mul_left_left]
  exact terminalC_coprime hp i

noncomputable def terminalLeftUnit
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) : UnitClass (p ^ N) :=
  ZMod.unitOfCoprime (terminalLeftNat p N i)
    (terminalLeftNat_coprime hp hN i)

noncomputable def terminalRightUnit
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) : UnitClass (p ^ N) :=
  ZMod.unitOfCoprime (terminalRightNat p N i)
    (terminalRightNat_coprime hp hN i)

theorem terminalLeftNat_lt_modulus
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalLeftNat p N i < p ^ N := by
  have hc := terminalC_lt hp.two_le i
  have hy := terminalY_lt i
  have hp0 := hp.pos
  let P := p ^ (N - 2)
  have htail : terminalC i + p * terminalY i < p * P := by
    calc
      terminalC i + p * terminalY i < p * (terminalY i + 1) := by
        nlinarith
      _ ≤ p * P := Nat.mul_le_mul_left p (by simpa [P] using hy)
  have hlead : (terminalC i + 1) * (p * P) ≤ p * (p * P) :=
    Nat.mul_le_mul_right (p * P) (by omega)
  have hpow : p ^ N = p * p * p ^ (N - 2) := by
    calc
      p ^ N = p ^ ((N - 2) + 2) := by congr 1; omega
      _ = p ^ (N - 2) * p ^ 2 := by rw [pow_add]
      _ = p * p * p ^ (N - 2) := by ring
  rw [terminalLeftNat_eq_coarse hN, hpow]
  change terminalC i + p * (terminalC i * P + terminalY i) < p * p * P
  calc
    terminalC i + p * (terminalC i * P + terminalY i) =
        terminalC i * (p * P) +
          (terminalC i + p * terminalY i) := by ring
    _ < terminalC i * (p * P) + p * P :=
      Nat.add_lt_add_left htail _
    _ = (terminalC i + 1) * (p * P) := by ring
    _ ≤ p * (p * P) := hlead
    _ = p * p * P := by ring

theorem terminalRightNat_lt_modulus
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalRightNat p N i < p ^ N := by
  have hc := terminalC_lt hp.two_le i
  have hy := terminalY_lt i
  have hp0 := hp.pos
  let P := p ^ (N - 2)
  have htail : terminalC i + p * terminalY i < p * P := by
    calc
      terminalC i + p * terminalY i < p * (terminalY i + 1) := by
        nlinarith
      _ ≤ p * P := Nat.mul_le_mul_left p (by simpa [P] using hy)
  have hlead : terminalC i * (p * P) ≤ p * (p * P) :=
    Nat.mul_le_mul_right (p * P) hc.le
  have hpow : p ^ N = p * p * p ^ (N - 2) := by
    calc
      p ^ N = p ^ ((N - 2) + 2) := by congr 1; omega
      _ = p ^ (N - 2) * p ^ 2 := by rw [pow_add]
      _ = p * p * p ^ (N - 2) := by ring
  rw [terminalRightNat_eq_coarse hN, hpow]
  change terminalC i + p * ((terminalC i - 1) * P + terminalY i) <
    p * p * P
  calc
    terminalC i + p * ((terminalC i - 1) * P + terminalY i) =
        (terminalC i - 1) * (p * P) +
          (terminalC i + p * terminalY i) := by ring
    _ < (terminalC i - 1) * (p * P) + p * P :=
      Nat.add_lt_add_left htail _
    _ = terminalC i * (p * P) := by
      calc
        (terminalC i - 1) * (p * P) + p * P =
            ((terminalC i - 1) + 1) * (p * P) := by ring
        _ = _ := by rw [Nat.sub_add_cancel (terminalC_pos i)]
    _ ≤ p * (p * P) := hlead
    _ = p * p * P := by ring

theorem terminalNat_mod_p_left
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalLeftNat p N i % p = terminalC i := by
  rw [terminalLeftNat_eq_coarse hN]
  simp [Nat.mod_eq_of_lt (terminalC_lt hp.two_le i)]

theorem terminalNat_mod_p_right
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalRightNat p N i % p = terminalC i := by
  rw [terminalRightNat_eq_coarse hN]
  simp [Nat.mod_eq_of_lt (terminalC_lt hp.two_le i)]

theorem terminalLeftUnit_injective
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N) :
    Function.Injective (terminalLeftUnit hp hN) := by
  intro i j hij
  have hv := congrArg Units.val hij
  unfold terminalLeftUnit at hv
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hv
  have hn : terminalLeftNat p N i = terminalLeftNat p N j := by
    have := congrArg ZMod.val hv
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt (terminalLeftNat_lt_modulus hp hN i),
      Nat.mod_eq_of_lt (terminalLeftNat_lt_modulus hp hN j)] using this
  have hc : terminalC i = terminalC j := by
    calc
      terminalC i = terminalLeftNat p N i % p :=
        (terminalNat_mod_p_left hp hN i).symm
      _ = terminalLeftNat p N j % p := by rw [hn]
      _ = terminalC j := terminalNat_mod_p_left hp hN j
  apply Prod.ext
  · apply Fin.ext
    unfold terminalC at hc
    omega
  · apply Fin.ext
    rw [terminalLeftNat_eq_coarse hN, terminalLeftNat_eq_coarse hN, hc] at hn
    unfold terminalY at hn
    have hmul := Nat.add_left_cancel hn
    have hinner := Nat.mul_left_cancel hp.pos hmul
    have hy := Nat.add_left_cancel hinner
    exact hy

theorem terminalRightUnit_injective
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N) :
    Function.Injective (terminalRightUnit hp hN) := by
  intro i j hij
  have hv := congrArg Units.val hij
  unfold terminalRightUnit at hv
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hv
  have hn : terminalRightNat p N i = terminalRightNat p N j := by
    have := congrArg ZMod.val hv
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt (terminalRightNat_lt_modulus hp hN i),
      Nat.mod_eq_of_lt (terminalRightNat_lt_modulus hp hN j)] using this
  have hc : terminalC i = terminalC j := by
    calc
      terminalC i = terminalRightNat p N i % p :=
        (terminalNat_mod_p_right hp hN i).symm
      _ = terminalRightNat p N j % p := by rw [hn]
      _ = terminalC j := terminalNat_mod_p_right hp hN j
  apply Prod.ext
  · apply Fin.ext
    unfold terminalC at hc
    omega
  · apply Fin.ext
    rw [terminalRightNat_eq_coarse hN, terminalRightNat_eq_coarse hN, hc] at hn
    unfold terminalY at hn
    have hmul := Nat.add_left_cancel hn
    have hinner := Nat.mul_left_cancel hp.pos hmul
    have hy := Nat.add_left_cancel hinner
    exact hy

theorem terminalUnits_disjoint
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i j : TerminalUnitIndex p N) :
    terminalLeftUnit hp hN i ≠ terminalRightUnit hp hN j := by
  intro hij
  have hv := congrArg Units.val hij
  unfold terminalLeftUnit terminalRightUnit at hv
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hv
  have hn : terminalLeftNat p N i = terminalRightNat p N j := by
    have := congrArg ZMod.val hv
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt (terminalLeftNat_lt_modulus hp hN i),
      Nat.mod_eq_of_lt (terminalRightNat_lt_modulus hp hN j)] using this
  have hc : terminalC i = terminalC j := by
    calc
      terminalC i = terminalLeftNat p N i % p :=
        (terminalNat_mod_p_left hp hN i).symm
      _ = terminalRightNat p N j % p := by rw [hn]
      _ = terminalC j := terminalNat_mod_p_right hp hN j
  have hyi := terminalY_lt i
  have hyj := terminalY_lt j
  have hp0 := hp.pos
  rw [terminalLeftNat_eq_coarse hN, terminalRightNat_eq_coarse hN, hc] at hn
  have hmul := Nat.add_left_cancel hn
  have hinner := Nat.mul_left_cancel hp0 hmul
  have hP : 0 < p ^ (N - 2) := pow_pos hp0 _
  have hright :
      (terminalC j - 1) * p ^ (N - 2) + terminalY j <
        terminalC j * p ^ (N - 2) := by
    calc
      (terminalC j - 1) * p ^ (N - 2) + terminalY j <
          (terminalC j - 1) * p ^ (N - 2) + p ^ (N - 2) :=
        Nat.add_lt_add_left hyj _
      _ = terminalC j * p ^ (N - 2) := by
        calc
          (terminalC j - 1) * p ^ (N - 2) + p ^ (N - 2) =
              ((terminalC j - 1) + 1) * p ^ (N - 2) := by ring
          _ = _ := by rw [Nat.sub_add_cancel (terminalC_pos j)]
  have hleft : terminalC j * p ^ (N - 2) ≤
      terminalC j * p ^ (N - 2) + terminalY i := Nat.le_add_right _ _
  omega

noncomputable def terminalReflection {p N : ℕ} :
    TerminalUnitIndex p N ≃ TerminalUnitIndex p N :=
  (Fin.revPerm : Equiv.Perm (Fin (p - 1))).prodCongr
    (Fin.revPerm : Equiv.Perm (Fin (p ^ (N - 2))))

theorem terminalReflection_C
    {p N : ℕ} (hp : 2 ≤ p) (i : TerminalUnitIndex p N) :
    terminalC (terminalReflection i) = p - terminalC i := by
  unfold terminalReflection terminalC
  simp [Fin.rev]
  omega

theorem terminalReflection_Y
    {p N : ℕ} (i : TerminalUnitIndex p N) :
    terminalY (terminalReflection i) = p ^ (N - 2) - 1 - terminalY i := by
  unfold terminalReflection terminalY
  simp [Fin.rev]
  omega

theorem terminalLeft_add_reflectedRight
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalLeftNat p N i + terminalRightNat p N (terminalReflection i) =
      p ^ N := by
  have hc := terminalC_pos i
  have hclt := terminalC_lt hp.two_le i
  have hy := terminalY_lt i
  have hpow : p ^ N = p * p * p ^ (N - 2) := by
    calc
      p ^ N = p ^ ((N - 2) + 2) := by congr 1; omega
      _ = p ^ (N - 2) * p ^ 2 := by rw [pow_add]
      _ = p * p * p ^ (N - 2) := by ring
  rw [terminalLeftNat_eq_coarse hN, terminalRightNat_eq_coarse hN,
    terminalReflection_C hp.two_le, terminalReflection_Y,
    hpow]
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub (by omega : 1 ≤ p - terminalC i)]
  rw [Nat.cast_sub hclt.le]
  rw [Nat.cast_sub (by omega : terminalY i ≤ p ^ (N - 2) - 1)]
  rw [Nat.cast_sub (by omega : 1 ≤ p ^ (N - 2))]
  push_cast
  ring

theorem terminalRight_add_reflectedLeft
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    terminalRightNat p N i + terminalLeftNat p N (terminalReflection i) =
      p ^ N := by
  have hc := terminalC_pos i
  have hclt := terminalC_lt hp.two_le i
  have hy := terminalY_lt i
  have hpow : p ^ N = p * p * p ^ (N - 2) := by
    calc
      p ^ N = p ^ ((N - 2) + 2) := by congr 1; omega
      _ = p ^ (N - 2) * p ^ 2 := by rw [pow_add]
      _ = p * p * p ^ (N - 2) := by ring
  rw [terminalRightNat_eq_coarse hN, terminalLeftNat_eq_coarse hN,
    terminalReflection_C hp.two_le, terminalReflection_Y,
    hpow]
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub (by omega : 1 ≤ terminalC i)]
  rw [Nat.cast_sub hclt.le]
  rw [Nat.cast_sub (by omega : terminalY i ≤ p ^ (N - 2) - 1)]
  rw [Nat.cast_sub (by omega : 1 ≤ p ^ (N - 2))]
  push_cast
  ring

theorem terminal_neg_left_eq_reflected_right
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    -(terminalLeftUnit hp hN i) =
      terminalRightUnit hp hN (terminalReflection i) := by
  apply Units.ext
  rw [Units.val_neg]
  unfold terminalLeftUnit terminalRightUnit
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  have hsum := terminalLeft_add_reflectedRight hp hN i
  have hz :
      (terminalLeftNat p N i : ZMod (p ^ N)) +
        (terminalRightNat p N (terminalReflection i) : ZMod (p ^ N)) = 0 := by
    rw [← Nat.cast_add, hsum]
    simp
  apply sub_eq_zero.mp
  calc
    -(terminalLeftNat p N i : ZMod (p ^ N)) -
        (terminalRightNat p N (terminalReflection i) : ZMod (p ^ N)) =
      -((terminalLeftNat p N i : ZMod (p ^ N)) +
        (terminalRightNat p N (terminalReflection i) : ZMod (p ^ N))) := by ring
    _ = 0 := by rw [hz]; simp

theorem terminal_neg_right_eq_reflected_left
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    -(terminalRightUnit hp hN i) =
      terminalLeftUnit hp hN (terminalReflection i) := by
  apply Units.ext
  rw [Units.val_neg]
  unfold terminalRightUnit terminalLeftUnit
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  have hsum := terminalRight_add_reflectedLeft hp hN i
  have hz :
      (terminalRightNat p N i : ZMod (p ^ N)) +
        (terminalLeftNat p N (terminalReflection i) : ZMod (p ^ N)) = 0 := by
    rw [← Nat.cast_add, hsum]
    simp
  apply sub_eq_zero.mp
  calc
    -(terminalRightNat p N i : ZMod (p ^ N)) -
        (terminalLeftNat p N (terminalReflection i) : ZMod (p ^ N)) =
      -((terminalRightNat p N i : ZMod (p ^ N)) +
        (terminalLeftNat p N (terminalReflection i) : ZMod (p ^ N))) := by ring
    _ = 0 := by rw [hz]; simp

theorem terminalRight_add_modulusStep_eq_left
    {p N : ℕ} (i : TerminalUnitIndex p N) :
    terminalRightNat p N i + p ^ (N - 1) = terminalLeftNat p N i := by
  unfold terminalRightNat terminalLeftNat
  calc
    (terminalC i - 1) * p ^ (N - 1) + p * terminalY i + terminalC i +
        p ^ (N - 1) =
      ((terminalC i - 1) + 1) * p ^ (N - 1) +
        p * terminalY i + terminalC i := by ring
    _ = _ := by rw [Nat.sub_add_cancel (terminalC_pos i)]

theorem terminal_coarse_pair
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (i : TerminalUnitIndex p N) :
    previousUnit (p := p) (N := N) (by omega)
        (terminalLeftUnit hp hN i) =
      previousUnit (p := p) (N := N) (by omega)
        (terminalRightUnit hp hN i) := by
  apply Units.ext
  unfold previousUnit terminalLeftUnit terminalRightUnit
  simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  have hnat := terminalRight_add_modulusStep_eq_left i
  have hcast := congrArg
    (fun z : ℕ => (z : ZMod (p ^ (N - 1)))) hnat
  push_cast at hcast
  have hzero :
      (p : ZMod (p ^ (N - 1))) ^ (N - 1) = 0 := by
    rw [← Nat.cast_pow]
    simp
  rw [hzero, add_zero] at hcast
  rw [ZMod.cast_natCast (primePower_previous_dvd (p := p) (N := N) (by omega)),
    ZMod.cast_natCast (primePower_previous_dvd (p := p) (N := N) (by omega))]
  simpa using hcast.symm

noncomputable def terminalUnitBoundary
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N) :
    UnitClass (p ^ N) → ℂ := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact pairedBoundary (terminalLeftUnit hp hN) (terminalRightUnit hp hN)

theorem terminalUnitBoundary_conductorBalance
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hN : 2 ≤ N)
    (r : UnitClass (p ^ (N - 1))) :
    ∑ x : UnitClass (p ^ N) with
        previousUnit (p := p) (N := N) (by omega) x = r,
      terminalUnitBoundary hp hN x = 0 := by
  exact pairedBoundary_fiber_balance
    (terminalLeftUnit hp hN) (terminalRightUnit hp hN)
    (previousUnit (p := p) (N := N) (by omega))
    (terminal_coarse_pair hp hN) r

theorem terminalUnitBoundary_odd
    {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N)
    (x : UnitClass (p ^ N)) :
    terminalUnitBoundary hp hN (-x) = -terminalUnitBoundary hp hN x := by
  exact pairedBoundary_odd
    (terminalLeftUnit hp hN) (terminalRightUnit hp hN)
    terminalReflection terminalReflection
    (terminal_neg_right_eq_reflected_left hp hN)
    (terminal_neg_left_eq_reflected_right hp hN) x

theorem terminalUnitBoundary_norm
    {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 2 ≤ N) :
    ∑ x : UnitClass (p ^ N), ‖terminalUnitBoundary hp hN x‖ ^ 2 =
      2 * (p ^ (N - 2) : ℝ) * (p - 1) := by
  change (∑ x : UnitClass (p ^ N),
      ‖pairedBoundary (terminalLeftUnit hp hN)
        (terminalRightUnit hp hN) x‖ ^ 2) = _
  rw [pairedBoundary_normSq_sum
    (terminalLeftUnit hp hN) (terminalRightUnit hp hN)
    (terminalLeftUnit_injective hp hN)
    (terminalRightUnit_injective hp hN)
    (terminalUnits_disjoint hp hN)]
  simp only [TerminalUnitIndex, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  ring

def terminalFormalBoundarySize (p N : ℕ) : ℕ :=
  2 * p ^ (N - 1)

theorem terminalUnitBoundary_meanLaw
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N) :
    primitiveOddBoundaryMomentReal (terminalUnitBoundary hp hN) /
        (primitiveOddCharacterCount (p ^ N) : ℝ) =
      2 * terminalFormalBoundarySize p N := by
  rw [boundaryMeanCriterion_average hp hpodd hN
    (terminalUnitBoundary hp hN)
    (terminalUnitBoundary_conductorBalance hp hN)
    (terminalUnitBoundary_odd hp hN)]
  rw [terminalUnitBoundary_norm hp hN]
  unfold terminalFormalBoundarySize
  have hpcast : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have hpow : p ^ (N - 1) = p * p ^ (N - 2) := by
    have he : N - 1 = (N - 2) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [hpow]
  push_cast
  field_simp [hpcast]

end NField.Alignment.TerminalCollisionBoundary
