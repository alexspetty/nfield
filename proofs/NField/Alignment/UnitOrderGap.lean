/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# An interval without unit orders

For q at least five, no unit modulo q has order in [q/2,2q/3).
The integer inequalities are cross-multiplied, so no floor approximation is
introduced. A large order must equal the totient by Lagrange. Mathlib's proved
classification of cyclic unit groups then reduces the contradiction to the
totient of an odd prime power or twice an odd prime power.

This proves Lemma 11 of "Repetend Rigidity at the Golden Scale" for every unit,
not just a bounded sample of positional bases. The q=4 exception is retained.
-/

namespace NField.Alignment

/-- A unit order at least half the modulus must exhaust the unit group. -/
theorem unit_order_eq_totient_of_half_le {q : ℕ} (hq : 1 < q)
    (u : (ZMod q)ˣ) (hlo : q ≤ 2 * orderOf u) :
    orderOf u = q.totient := by
  letI : NeZero q := ⟨by omega⟩
  have hdiv : orderOf u ∣ q.totient := by
    simpa only [ZMod.card_units_eq_totient] using (orderOf_dvd_card (x := u))
  have hh : 0 < orderOf u := orderOf_pos u
  have hlt := Nat.totient_lt q hq
  obtain ⟨k, hk⟩ := hdiv
  have hk1 : k = 1 := by
    have ht : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    nlinarith
  simpa [hk1] using hk.symm

/-- For every modulus at least five, no unit order lies from half the modulus
up to, but excluding, two thirds of the modulus. -/
theorem unit_order_gap {q : ℕ} (hq : 5 ≤ q) (u : (ZMod q)ˣ) :
    ¬ (q ≤ 2 * orderOf u ∧ 3 * orderOf u < 2 * q) := by
  rintro ⟨hlo, hhi⟩
  letI : NeZero q := ⟨by omega⟩
  have heq := unit_order_eq_totient_of_half_le (by omega) u hlo
  have hcyc : IsCyclic (ZMod q)ˣ := by
    apply isCyclic_of_orderOf_eq_card u
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using heq
  have hc := (ZMod.isCyclic_units_iff q).mp hcyc
  rcases hc with h | h | h | h | ⟨p, m, hp, hodd, hm, hpm⟩
  · omega
  · omega
  · omega
  · omega
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hne : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      omega
    omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hpow : 0 < p ^ a := pow_pos hp.pos _
  rcases hpm with hpm | hpm
  · rw [heq, hpm, Nat.totient_prime_pow_succ hp, pow_succ] at hhi
    nlinarith
  · rw [heq, hpm, Nat.totient_two_mul_of_odd (hodd.pow),
      Nat.totient_prime_pow_succ hp, pow_succ] at hlo
    nlinarith


end NField.Alignment
