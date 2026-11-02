/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanTwoPowerBound
import NField.Alignment.KloostermanOddPrimePowerBound
import NField.Alignment.KloostermanEvenPrimePowerBound
import NField.Alignment.KloostermanPrimeBound

/-!
# Primitive prime-power estimates with both phase parameters

Inversion swaps the two parameters in the actual unit sum. This permits
one uniform theorem at every positive prime-power exponent whenever at
least one phase parameter is a unit. The odd-prime constant stays two;
the exceptional prime two has a single absolute constant eight.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimitivePrimePowerBound
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase InverseAdditiveCompletion
  KloostermanPrimePowerStationary KloostermanTraceSum KloostermanPrimeBound
  KloostermanEvenPrimePowerBound KloostermanOddPrimePowerBound KloostermanTwoPowerBound

/-- Inversion swaps the actual two-parameter unit sum over any finite commutative ring. -/
theorem unitSum_swap {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (a b : R) : unitSum ψ a b=unitSum ψ b a := by
  unfold unitSum
  rw [← Equiv.sum_comp (Equiv.inv Rˣ) (fun u => ψ (phase b a u))]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Equiv.inv_apply,phase,inv_inv,add_comm]

/-- The literal unit sum at a prime obeys the bound with either parameter nonzero. -/
theorem prime_unitSum_bound (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hab : IsUnit a ∨ IsUnit b) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤ 2*Real.sqrt p := by
  have he := complete_inverse_eq_unitSum (q := p) 1 b (-a)
  simp only [neg_neg,Nat.cast_one,mul_one] at he
  rw [← he,complete_inverse_eq_traceKloosterman]
  have hb := prime_trace_sum_bound_all p a b 1
    (hab.elim (fun h => Or.inl h.ne_zero) (fun h => Or.inr h.ne_zero)) one_ne_zero
  simpa only [neg_neg,Nat.cast_one,mul_one] using hb

/-- At positive exponents of odd primes, either unit phase parameter suffices. -/
theorem odd_prime_unitSum_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k : ℕ) (hk : 1≤k) (a b : ZMod (p^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤ 2*Real.sqrt ((p^k:ℕ):ℝ) := by
  by_cases hk1 : k=1
  · subst k
    have hb (q : ℕ) [NeZero q] (hq : q=p)
        (a b : ZMod q) (hab : IsUnit a ∨ IsUnit b) :
        ‖unitSum ZMod.stdAddChar a b‖ ≤ 2*Real.sqrt q := by
      subst q
      exact prime_unitSum_bound p a b hab
    exact hb (p^1) (pow_one p) a b hab
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · obtain ⟨h,rfl⟩ : ∃ h, k=2*h := ⟨k/2,by omega⟩
    have he := complete_inverse_eq_unitSum (q := p^(2*h)) 1 b (-a)
    simp only [neg_neg,Nat.cast_one,mul_one] at he
    rw [← he]
    apply even_prime_power_bound p hp h (by omega) 1 b (-a)
    simpa only [neg_neg,Nat.cast_one,mul_one] using hab
  · obtain ⟨h,rfl⟩ : ∃ h, k=2*h+1 := ⟨k/2,by omega⟩
    have hh : 1≤h := by omega
    rcases hab with ha | hb
    · rw [unitSum_swap]
      simpa only [odd_sqrt_factor] using norm_unitSum_le p hp h hh b a ha
    · simpa only [odd_sqrt_factor] using norm_unitSum_le p hp h hh a b hb

/-- At powers of two a single constant eight is uniform in the positive exponent. -/
theorem two_power_unitSum_bound (k : ℕ) (hk : 1≤k)
    (a b : ZMod (2^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) := by
  by_cases hk1 : k=1
  · subst k
    have hb := prime_unitSum_bound 2 a b hab
    norm_num only [Nat.cast_ofNat] at hb
    simp only [pow_one,Nat.cast_ofNat]
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  · have he := complete_inverse_eq_unitSum (q := 2^k) 1 b (-a)
    simp only [neg_neg,Nat.cast_one,mul_one] at he
    rw [← he]
    apply two_power_bound k (by omega) 1 b (-a)
    simpa only [neg_neg,Nat.cast_one,mul_one] using hab

/-- The actual primitive unit sum at every prime power, retaining the sharper odd-prime constant. -/
theorem prime_power_unitSum_bound (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1≤k)
    (a b : ZMod (p^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤ (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ) := by
  by_cases hp : p=2
  · subst p
    simpa only [ite_true] using two_power_unitSum_bound k hk a b hab
  · simpa only [if_neg hp] using odd_prime_unitSum_bound p hp k hk a b hab

/-- Unit frequency and coprime multiplier give all positive prime-power exponents and every t. -/
theorem complete_prime_power_bound_unit_frequency (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 1≤k) (r : ℕ) (j t : ZMod (p^k))
    (hr : r.Coprime (p^k)) (hj : IsUnit j) :
    ‖completeInverseSum r j t‖ ≤ (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ) := by
  rw [complete_inverse_eq_unitSum]
  exact prime_power_unitSum_bound p k hk (-t) (j*r)
    (Or.inr (hj.mul ((ZMod.isUnit_iff_coprime r (p^k)).mpr hr)))

end NField.Alignment.PrimitivePrimePowerBound
