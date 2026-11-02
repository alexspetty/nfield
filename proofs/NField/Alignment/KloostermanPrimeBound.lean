/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanRootModuli

/-!
# Complete inverse-sum bound at every prime

The odd-prime root estimate is joined to exact degenerate character sums
and the elementary characteristic-two bound. The original complete sum
is bounded at every completion frequency, including zero.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanPrimeBound
open scoped BigOperators Classical
open KloostermanTraceSum KloostermanRootModuli InverseAdditiveCompletion

/-- Inversion permutes the actual nonzero summation variables. -/
theorem trace_sum_swap {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) (m : ZMod p) :
    traceKloostermanSum p a b m = traceKloostermanSum p b a m := by
  unfold traceKloostermanSum
  have hperm := Equiv.sum_comp (Equiv.inv K)
    (fun t : K => if t=0 then (0:ℂ) else
      ZMod.stdAddChar (m*Algebra.trace (ZMod p) K (b*t+a/t)))
  rw [← hperm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.inv_apply,inv_eq_zero,div_inv_eq_mul]
  split_ifs
  · rfl
  · congr 1
    congr 1
    apply congrArg (Algebra.trace (ZMod p) K)
    ring

/-- With one zero parameter the nontrivial prime-field character sum is -1. -/
theorem prime_trace_sum_zero_right (p : ℕ) [Fact p.Prime]
    (a m : ZMod p) (ha : a≠0) (hm : m≠0) :
    traceKloostermanSum p a 0 m = -1 := by
  have ho := prime_character_orthogonality p (m*a)
  rw [if_neg (mul_ne_zero hm ha)] at ho
  have hs := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun t => ZMod.stdAddChar (t*(m*a))) (Finset.mem_univ 0)
  simp only [zero_mul,AddChar.map_zero_eq_one,ho] at hs
  have he : traceKloostermanSum p a 0 m =
      ∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0, ZMod.stdAddChar (t*(m*a)) := by
    unfold traceKloostermanSum
    simp only [Algebra.trace_self_apply,zero_div,add_zero]
    rw [Finset.sum_ite,Finset.filter_eq',Finset.filter_ne']
    simp only [Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    ring
  rw [he]
  linear_combination hs

/-- The triangle inequality bounds any prime-field trace sum by p-1. -/
theorem prime_trace_sum_trivial (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    ‖traceKloostermanSum p a b m‖ ≤ (p:ℝ)-1 := by
  unfold traceKloostermanSum
  calc
    _ ≤ ∑ t : ZMod p, ‖if t=0 then (0:ℂ) else
        ZMod.stdAddChar (m*Algebra.trace (ZMod p) (ZMod p) (a*t+b/t))‖ := norm_sum_le _ _
    _ = (p:ℝ)-1 := by
      simp only [apply_ite norm,norm_zero,AddChar.norm_apply]
      simp [Finset.sum_ite,Finset.filter_ne',Nat.cast_sub (Fact.out : p.Prime).pos]

/-- Weil's square-root bound for every prime, including p=2 and one zero
parameter, at every nonzero character frequency. -/
theorem prime_trace_sum_bound_all (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (hab : a≠0 ∨ b≠0) (hm : m≠0) :
    ‖traceKloostermanSum p a b m‖ ≤ 2*Real.sqrt p := by
  have hs : 1≤Real.sqrt (p:ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  by_cases ha : a=0
  · have hb : b≠0 := hab.resolve_left (by simp [ha])
    rw [ha,trace_sum_swap,prime_trace_sum_zero_right p b m hb hm,norm_neg,norm_one]
    linarith
  by_cases hb : b=0
  · rw [hb,prime_trace_sum_zero_right p a m ha hm,norm_neg,norm_one]
    linarith
  rcases (Fact.out : p.Prime).eq_two_or_odd with hp | hp
  · subst p
    have ht := prime_trace_sum_trivial 2 a b m
    norm_num at ht
    linarith
  · exact prime_trace_sum_bound p (Nat.odd_iff.mpr hp) a b m ha hb hm

/-- The literal complete inverse sum is bounded at all prime moduli and
all completion frequencies; the input j is nonzero and r is coprime to p. -/
theorem complete_inverse_sum_prime_bound (p : ℕ) [Fact p.Prime]
    (r : ℕ) (j t : ZMod p) (hr : r.Coprime p) (hj : j≠0) :
    ‖completeInverseSum r j t‖ ≤ 2*Real.sqrt p := by
  rw [complete_inverse_eq_traceKloosterman]
  apply prime_trace_sum_bound_all
  · right
    exact mul_ne_zero hj (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime r p).mpr hr))
  · exact one_ne_zero

end NField.Alignment.KloostermanPrimeBound
