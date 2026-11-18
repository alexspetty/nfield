/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrimitiveBasis
/-! # Exact finite primitive-pair exclusion on the arithmetic torus -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators ArithmeticFunction.zeta

def primitiveAt (n a b : ℕ) : Prop := (a.gcd b).Coprime n

instance primitiveAtDecidable (n a b : ℕ) : Decidable (primitiveAt n a b) :=
  inferInstanceAs (Decidable ((a.gcd b).Coprime n))

def primitivePoints (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter (fun ab => primitiveAt n ab.1 ab.2)

def primitiveSum (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, if primitiveAt n a b then f a else 0

theorem primitive_at_iff (n a b : ℕ) :
    primitiveAt n a b ↔ (a.gcd n).Coprime b := by
  simp only [primitiveAt, Nat.Coprime, Nat.gcd_assoc]
  rw [Nat.gcd_comm b n]

theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))=if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem primitive_indicator {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    (if primitiveAt n a b then (1 : ℝ) else 0)=
      ∑ d ∈ n.divisors, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg := Nat.gcd_pos_of_pos_right (a.gcd b) hn
  have hset : n.divisors.filter (fun d => d ∣ a ∧ d ∣ b)=((a.gcd b).gcd n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hn0 := hn.ne'
    have hg0 := hg.ne'
    tauto
  rw [← Finset.sum_filter, hset, moebius_divisor_sum]
  rfl

theorem torus_multiples_sum {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.range n, if d ∣ a then f a else 0)=
      ∑ a ∈ Finset.range (n/d), f (d*a) := by
  have hdp := Nat.pos_of_dvd_of_pos hd hn
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => d*a) ?_ ?_ ?_ ?_
  · intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,dvd_mul_right d a⟩
    have he := Nat.mul_div_cancel' hd
    have hlt := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp ha) hdp
    omega
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hdp hab
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha,had⟩
    refine ⟨a/d,Finset.mem_range.mpr ?_,Nat.mul_div_cancel' had⟩
    apply (Nat.div_lt_iff_lt_mul hdp).mpr
    rw [Nat.div_mul_cancel hd]
    exact Finset.mem_range.mp ha
  · intro a ha
    rfl

theorem primitive_weighted_indicator {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (a b : ℕ) :
    (if primitiveAt n a b then f a else 0)=
      ∑ d ∈ n.divisors, if d ∣ a ∧ d ∣ b then
        (ArithmeticFunction.moebius d : ℝ)*f a else 0 := by
  have h := congrArg (fun r : ℝ => r*f a) (primitive_indicator hn a b)
  rw [Finset.sum_mul] at h
  simpa only [ite_mul, one_mul, zero_mul] using h

theorem primitive_sum_exclusion {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) :
    primitiveSum n f=∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)*
        ∑ a ∈ Finset.range (n/d), f (d*a) := by
  unfold primitiveSum
  simp_rw [primitive_weighted_indicator hn f]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hrow (a : ℕ) :
      (∑ b ∈ Finset.range n, if d ∣ a ∧ d ∣ b then
        (ArithmeticFunction.moebius d : ℝ)*f a else 0)=
          if d ∣ a then ((n/d : ℕ) : ℝ)*(ArithmeticFunction.moebius d : ℝ)*f a else 0 := by
    by_cases ha : d ∣ a
    · simp only [ha, true_and, if_true]
      rw [torus_multiples_sum hn hdiv]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    · simp only [ha, false_and, if_false, Finset.sum_const_zero]
  simp_rw [hrow]
  rw [torus_multiples_sum hn hdiv]
  rw [← Finset.mul_sum]
  ring

theorem primitive_sum_one_eq_card (n : ℕ) :
    primitiveSum n (fun _ => 1)=((primitivePoints n).card : ℝ) := by
  simp only [primitivePoints, Finset.card_eq_sum_ones, primitiveSum]
  push_cast
  rw [Finset.sum_filter, Finset.sum_product]

end NField.ResetForests.PrimitiveCoordinates
