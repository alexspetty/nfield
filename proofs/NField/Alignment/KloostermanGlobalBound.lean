/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanCRT
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction

/-!
# General-modulus complete inverse-sum estimate

A multiplicative exceptional factor accounts for the prime two only once.
Prime-power gcd bounds and exact CRT then imply the manuscript's divisor-
and gcd-weighted estimate, with explicit absolute constant four.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanGlobalBound
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase PrimePowerGcdBound KloostermanCRT
  InverseAdditiveCompletion KloostermanPrimePowerStationary

/-- The prime-two loss is charged once, independently of the number of odd factors. -/
def exceptionalFactor (q : ℕ) : ℝ := if 2∣q then 4 else 1

/-- The global arithmetic coefficient retains the actual divisor count. -/
def divisorCost (q : ℕ) : ℝ := exceptionalFactor q*q.divisors.card

theorem exceptionalFactor_bounds (q : ℕ) : 1≤exceptionalFactor q ∧ exceptionalFactor q≤4 := by
  unfold exceptionalFactor
  split_ifs <;> norm_num

theorem divisorCost_nonneg (q : ℕ) : 0≤divisorCost q :=
  mul_nonneg (le_trans (by norm_num) (exceptionalFactor_bounds q).1) (Nat.cast_nonneg _)

/-- Coprime factors cannot both incur the prime-two loss. -/
theorem exceptionalFactor_mul (m n : ℕ) (h : m.Coprime n) :
    exceptionalFactor (m*n)=exceptionalFactor m*exceptionalFactor n := by
  have hnot : ¬(2∣m ∧ 2∣n) := by
    intro hd
    have hg := Nat.dvd_gcd hd.1 hd.2
    rw [h.gcd_eq_one] at hg
    norm_num at hg
  by_cases hm : 2∣m <;> by_cases hn : 2∣n
  all_goals first
    | exact False.elim (hnot ⟨hm,hn⟩)
    | simp only [exceptionalFactor,Nat.prime_two.dvd_mul,hm,hn,or_true,true_or,
        or_false,false_or,ite_true,ite_false,mul_one,one_mul]

/-- The cost is exactly multiplicative across coprime moduli. -/
theorem divisorCost_mul (m n : ℕ) (h : m.Coprime n) :
    divisorCost (m*n)=divisorCost m*divisorCost n := by
  simp only [divisorCost,exceptionalFactor_mul m n h,h.card_divisors_mul,Nat.cast_mul]
  ring

/-- Every nontrivial modulus has at least its two distinct endpoint divisors. -/
theorem two_le_card_divisors (q : ℕ) (hq : 2≤q) : 2≤q.divisors.card := by
  have hs : ({1,q}:Finset ℕ) ⊆ q.divisors := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_pair (by omega : (1:ℕ)≠q)] using hc

/-- The local prime-power constant is absorbed by the multiplicative divisor cost. -/
theorem localConstant_le_divisorCost (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k) :
    localConstant p≤divisorCost (p^k) := by
  have hq : 2≤p^k := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hd : (2:ℝ)≤(p^k).divisors.card := by exact_mod_cast two_le_card_divisors (p^k) hq
  by_cases hp : p=2
  · subst p
    have he : 2∣2^k := dvd_pow_self 2 (by omega)
    simp only [localConstant,ite_true,divisorCost,exceptionalFactor,if_pos he]
    linarith
  · have he := (exceptionalFactor_bounds (p^k)).1
    simp only [localConstant,if_neg hp,divisorCost]
    nlinarith

/-- Ring reduction preserves the gcd against the smaller modulus. -/
theorem gcd_reduction (q d : ℕ) [NeZero q] (hd : d∣q) (x : ZMod q) :
    Nat.gcd (ZMod.castHom hd (ZMod d) x).val d=Nat.gcd x.val d := by
  rw [ZMod.castHom_apply,ZMod.cast_eq_val,ZMod.val_natCast,(Nat.mod_modEq x.val d).gcd_eq]

/-- The literal unit sum at any positive modulus obeys the multiplicative-cost gcd estimate. -/
theorem unitSum_divisorCost_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖unitSum ZMod.stdAddChar a b‖≤
      divisorCost q*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd b.val q:ℝ) := by
  have hall : ∀ q, ∀ [NeZero q], ∀ a b : ZMod q,
      ‖unitSum ZMod.stdAddChar a b‖≤
        divisorCost q*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd b.val q:ℝ) := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p k hp hk inst a b
      letI : Fact p.Prime := ⟨hp⟩
      have hb := prime_power_unitSum_gcd_bound p k a b
      have hc := localConstant_le_divisorCost p k hk
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    · intro inst
      exact (NeZero.ne (0:ℕ) rfl).elim
    · intro inst a b
      have ha : a=0 := Subsingleton.elim _ _
      have hb : b=0 := Subsingleton.elim _ _
      subst a b
      simp [unitSum,phase,divisorCost,exceptionalFactor]
    · intro m n hm hn h ih_m ih_n inst a b
      letI : NeZero m := ⟨by omega⟩
      letI : NeZero n := ⟨by omega⟩
      rw [norm_unitSum_crt m n h]
      have hmB := ih_m (leftTwist m n*leftReduction m n a) (leftTwist m n*leftReduction m n b)
      have hnB := ih_n (rightTwist m n*rightReduction m n a) (rightTwist m n*rightReduction m n b)
      rw [left_twist_gcd m n h] at hmB
      rw [right_twist_gcd m n h] at hnB
      change _≤divisorCost m*Real.sqrt (m:ℝ)*
        Real.sqrt (Nat.gcd (ZMod.castHom (dvd_mul_right m n) (ZMod m) b).val m:ℝ) at hmB
      change _≤divisorCost n*Real.sqrt (n:ℝ)*
        Real.sqrt (Nat.gcd (ZMod.castHom (dvd_mul_left n m) (ZMod n) b).val n:ℝ) at hnB
      rw [gcd_reduction] at hmB hnB
      calc
        _ ≤ (divisorCost m*Real.sqrt (m:ℝ)*Real.sqrt (Nat.gcd b.val m:ℝ))*
            (divisorCost n*Real.sqrt (n:ℝ)*Real.sqrt (Nat.gcd b.val n:ℝ)) :=
          mul_le_mul hmB hnB (norm_nonneg _)
            (mul_nonneg (mul_nonneg (divisorCost_nonneg m) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        _ = _ := by
          rw [divisorCost_mul m n h,Nat.Coprime.gcd_mul b.val h,Nat.cast_mul,
            Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m),
            Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd b.val m))]
          ring
  exact hall q a b

/-- Uniform absolute constant four bounds the actual sum at all positive moduli. -/
theorem unitSum_uniform_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖unitSum ZMod.stdAddChar a b‖≤
      4*Real.sqrt (q:ℝ)*q.divisors.card*Real.sqrt (Nat.gcd b.val q:ℝ) := by
  have hb := unitSum_divisorCost_bound q a b
  have hc : divisorCost q≤4*q.divisors.card :=
    mul_le_mul_of_nonneg_right (exceptionalFactor_bounds q).2 (Nat.cast_nonneg _)
  calc
    _ ≤ (4*q.divisors.card)*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd b.val q:ℝ) :=
      hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- The original complete inverse sum, with the manuscript's exact gcd and divisor factors. -/
theorem complete_inverse_sum_bound (q : ℕ) [NeZero q] (r : ℕ) (j t : ZMod q)
    (hr : r.Coprime q) :
    ‖completeInverseSum r j t‖≤
      4*Real.sqrt (q:ℝ)*q.divisors.card*Real.sqrt (Nat.gcd j.val q:ℝ) := by
  rw [complete_inverse_eq_unitSum]
  have hb := unitSum_uniform_bound q (-t) (j*r)
  rwa [gcd_val_mul_coprime q j r hr] at hb

/-- The full complete-sum estimate is proved, with explicit constant four. -/
theorem complete_inverse_sum_estimate : CompleteInverseSumEstimate := by
  refine ⟨4,by norm_num,?_⟩
  intro q hq
  letI : NeZero q := ⟨by omega⟩
  intro r j hr _hj t
  exact complete_inverse_sum_bound q r j t hr

/-- SEC-03's exact incomplete-prefix source estimate follows without an analytic input. -/
theorem weil_estermann_inverse_prefix_estimate :
    NField.Alignment.InverseResiduePrefixCompletion.WeilEstermannInversePrefixEstimate :=
  weil_estermann_prefix_of_complete complete_inverse_sum_estimate

end NField.Alignment.KloostermanGlobalBound
