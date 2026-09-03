/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRatioCompression
import NField.Alignment.TerminalCollisionBoundary

/-!
# The prime-square collision window

The first digit window is encoded intrinsically as units represented by
`1, ..., p-1` modulo `p^2`.  The manuscript's collision weight and Dedekind
energy are then direct specializations of the general ratio-compression
theorem.
-/

namespace NField.Alignment.PrimeSquareCollisionWindow

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.DedekindCollisionKernel

abbrev FirstWindowIndex (p : ℕ) := Fin (p - 1)

def firstWindowNat {p : ℕ} (i : FirstWindowIndex p) : ℕ := i.val + 1

theorem firstWindowNat_pos {p : ℕ} (i : FirstWindowIndex p) :
    0 < firstWindowNat i := by
  unfold firstWindowNat
  omega

theorem firstWindowNat_lt {p : ℕ} (hp : 2 ≤ p)
    (i : FirstWindowIndex p) : firstWindowNat i < p := by
  unfold firstWindowNat
  omega

theorem firstWindowNat_coprime
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    (firstWindowNat i).Coprime (p ^ 2) := by
  rw [Nat.coprime_pow_right_iff (by omega : 0 < 2)]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt
    (firstWindowNat_pos i) (firstWindowNat_lt hp.two_le i)

/-- The unit represented by one entry of the first digit window. -/
noncomputable def firstWindowUnit
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    UnitClass (p ^ 2) :=
  ZMod.unitOfCoprime (firstWindowNat i) (firstWindowNat_coprime hp i)

theorem firstWindowUnit_val
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    (firstWindowUnit hp i).val.val = firstWindowNat i := by
  unfold firstWindowUnit
  have hlt : firstWindowNat i < p ^ 2 := by
    have hp2 := hp.two_le
    have hi := firstWindowNat_lt hp2 i
    nlinarith
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt hlt]

theorem firstWindowUnit_injective
    {p : ℕ} (hp : p.Prime) :
    Function.Injective (firstWindowUnit hp) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg (fun u : UnitClass (p ^ 2) => u.val.val) hij
  rw [firstWindowUnit_val hp i, firstWindowUnit_val hp j] at hv
  unfold firstWindowNat at hv
  omega

/-- The exact first digit window inside the unit group modulo `p^2`. -/
noncomputable def firstCollisionWindow
    {p : ℕ} (hp : p.Prime) : Finset (UnitClass (p ^ 2)) :=
  Finset.univ.image (firstWindowUnit hp)

theorem firstCollisionWindow_card
    {p : ℕ} (hp : p.Prime) :
    (firstCollisionWindow hp).card = p - 1 := by
  unfold firstCollisionWindow
  rw [Finset.card_image_of_injective _ (firstWindowUnit_injective hp)]
  simp

/-- The manuscript's ratio multiplicity `w_p(v)`. -/
noncomputable def primeSquareCollisionWeight
    {p : ℕ} (hp : p.Prime) (v : UnitClass (p ^ 2)) : ℕ :=
  collisionRatioWeight (firstCollisionWindow hp) v

/-- The Dedekind form of the prime-square collision energy. -/
noncomputable def dedekindCollisionEnergy
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact 4 * weightedRatioSum (firstCollisionWindow hp) dedekindSum

/-- Weight-free prime-square double sum, with its nonzero-modulus instance
discharged from primality. -/
noncomputable def primeSquareCollisionDoubleSum
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact collisionDoubleSum (firstCollisionWindow hp) dedekindSum

/-- Off-diagonal part of the prime-square ratio sum. -/
noncomputable def primeSquareCollisionOffDiagonal
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact collisionOffDiagonal (firstCollisionWindow hp) dedekindSum

/-- The diagonal Dedekind value at ratio one. -/
noncomputable def primeSquareDiagonalDedekind
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact dedekindSum (m := p ^ 2) 1

/-- Closed form of the ratio-one prime-square Dedekind value. -/
theorem primeSquareDiagonalDedekind_eq
    {p : ℕ} (hp : p.Prime) :
    primeSquareDiagonalDedekind hp =
      (((p ^ 2 : ℕ) : ℂ) - 1) * (((p ^ 2 : ℕ) : ℂ) - 2) /
        (12 * ((p ^ 2 : ℕ) : ℂ)) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold primeSquareDiagonalDedekind
  exact dedekindSum_one (m := p ^ 2) (by nlinarith [hp.two_le])

/-- Exact removal of the collision weight in prime-square coordinates. -/
theorem dedekindCollisionEnergy_eq_doubleSum
    {p : ℕ} (hp : p.Prime) :
    dedekindCollisionEnergy hp =
      4 * primeSquareCollisionDoubleSum hp := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold dedekindCollisionEnergy primeSquareCollisionDoubleSum
  rw [weightedRatioSum_eq_collisionDoubleSum]

/-- Exact diagonal/off-diagonal split before any asymptotic estimate. -/
theorem dedekindCollisionEnergy_poleSplit
    {p : ℕ} (hp : p.Prime) :
    dedekindCollisionEnergy hp =
      4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp +
        4 * primeSquareCollisionOffDiagonal hp := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [dedekindCollisionEnergy_eq_doubleSum hp,
    show primeSquareCollisionDoubleSum hp =
      collisionDoubleSum (firstCollisionWindow hp) dedekindSum by rfl,
    collisionDoubleSum_diagonal_offDiagonal,
    firstCollisionWindow_card hp]
  change 4 * (↑(p - 1) * dedekindSum (m := p ^ 2) 1 +
      collisionOffDiagonal (firstCollisionWindow hp)
        (fun h => dedekindSum h)) =
    4 * ↑(p - 1) * dedekindSum (m := p ^ 2) 1 +
      4 * collisionOffDiagonal (firstCollisionWindow hp)
        (fun h => dedekindSum h)
  ring

/-- Exact closed value of the diagonal term in the collision energy. -/
theorem dedekindCollisionEnergy_diagonal_closed
    {p : ℕ} (hp : p.Prime) :
    4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp =
      ((p - 1 : ℕ) : ℂ) * (((p ^ 2 : ℕ) : ℂ) - 1) *
        (((p ^ 2 : ℕ) : ℂ) - 2) /
          (3 * ((p ^ 2 : ℕ) : ℂ)) := by
  rw [primeSquareDiagonalDedekind_eq hp]
  ring

end NField.Alignment.PrimeSquareCollisionWindow
