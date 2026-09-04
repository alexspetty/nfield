/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
import NField.CollisionDefinition

/-!
Definitions used by the Lean companion to
"Three and the Golden Ratio."

The paper compares all fractions at one common clearing depth.  `Supported`
records exactly the divisibility condition needed to choose that depth, and
`synchronizedAligned` is the resulting one-digit comparison after the common
power of the base has been removed.
-/

namespace NField.Alignment

/-- `m` is supported by base `b` when some power of `b` is divisible by `m`. -/
def Supported (b m : ℕ) : Prop :=
  ∃ D : ℕ, m ∣ b ^ D

/-- One is supported in every base. -/
theorem supported_one (b : ℕ) : Supported b 1 := by
  exact ⟨0, by simp⟩

/-- Every positive power of the base is supported by that base. -/
theorem supported_pow (b D : ℕ) : Supported b (b ^ D) := by
  exact ⟨D, dvd_rfl⟩

/-- In particular, the base itself is a supported denominator. -/
theorem supported_self (b : ℕ) : Supported b b := by
  exact ⟨1, by simp⟩

/-- The cofactor left by a supported clearing depth. -/
def clearingCofactor (b m D : ℕ) : ℕ :=
  b ^ D / m

/--
At a common clearing depth, a numerator is aligned when it terminates
(residue zero), or when its next one-digit periodic digit agrees with the
reference numerator one.
-/
def synchronizedAligned (b p u k : ℕ) : Prop :=
  k % p = 0 ∨
    NField.CollisionDefinition.digitBin b p ((k * u) % p) =
      NField.CollisionDefinition.digitBin b p (u % p)

/-- Number of representatives below `p*m` in one residue class modulo `p`. -/
def residueCount (p r m : ℕ) : ℕ :=
  Nat.count (fun k => k % p = r) (p * m)

/-- Number of terminating numerators in `1, ..., p*m-1`. -/
def terminatingNumeratorCount (p m : ℕ) : ℕ :=
  residueCount p 0 m - 1

/-- Number of numerators whose synchronized one-digit tail matches the reference. -/
def matchingNumeratorCount (p m : ℕ) : ℕ :=
  residueCount p 1 m

/-- Total aligned numerator count from the terminating and reference classes. -/
def alignedNumeratorCount (p m : ℕ) : ℕ :=
  terminatingNumeratorCount p m + matchingNumeratorCount p m

/-- The exact normalized alignment obtained from the synchronized class count. -/
def oneDigitAlignment (p m : ℕ) : ℚ :=
  (alignedNumeratorCount p m : ℚ) / (p * m - 1 : ℕ)

end NField.Alignment
