/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicTable
import NField.Alignment.CollisionFluctuationClosure

/-!
# The collision periodic table closure

The direct lag-one collision deviation reduces to the finite table at the
least positive residue modulo the square of the base.  This supplies the
direct-count bridge used by the manuscript-facing theorem map.
-/

namespace NField.Alignment.CollisionPeriodicTableClosure

open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionFluctuationClosure
open NField.Alignment.CollisionPeriodicTable

/-- Every admissible integer has the table value of its residue modulo
`b^2`, including integers smaller than `b^2`. -/
theorem directIntegerDeviation_eq_table_mod_square
    {b N : ℕ} (hb2 : 2 ≤ b) (_hN2 : 2 ≤ N)
    (hcop : N.Coprime b) :
    directIntegerDeviation b N =
      fluctuationTable b (N % (b ^ 2)) := by
  let m := b ^ 2
  let a := N % m
  have hcopPow : N.Coprime m := by
    simpa [m] using hcop.pow_right 2
  have hcopA : a.Coprime m := by
    simpa [a] using (ZMod.coprime_mod_iff_coprime N m).2 hcopPow
  have ha : 1 ≤ a := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro ha0
    have hmOne : m = 1 := by
      rw [ha0] at hcopA
      simpa using hcopA
    have hmLower : 4 ≤ m := by
      dsimp [m]
      nlinarith
    omega
  have halt : a < m := by
    apply Nat.mod_lt
    dsimp [m]
    positivity
  have hdecomp : m * (N / m) + a = N := by
    calc
      m * (N / m) + a = a + m * (N / m) := by omega
      _ = N := by simpa [a] using Nat.mod_add_div N m
  have htable := directIntegerDeviation_eq_fluctuationTable
    (b := b) (h := N / m) (a := a) hb2 ha (by simpa [m] using halt)
      (by simpa [m] using hcopA)
  rw [hdecomp] at htable
  simpa [a] using htable

/-- The exact small-base verification range follows from the universal direct
collision-to-table theorem. -/
theorem small_base_direct_collision_regression :
    ∀ b ∈ checkedSmallBases,
      ∀ N ∈ checkedInputs b,
        directIntegerDeviation b N =
          fluctuationTable b (N % (b ^ 2)) := by
  intro b hb N hN
  have hbRange := Finset.mem_Icc.mp hb
  have hNData := Finset.mem_filter.mp hN
  have hNRange := Finset.mem_Icc.mp hNData.1
  exact directIntegerDeviation_eq_table_mod_square hbRange.1 hNRange.1
    hNData.2

end NField.Alignment.CollisionPeriodicTableClosure
