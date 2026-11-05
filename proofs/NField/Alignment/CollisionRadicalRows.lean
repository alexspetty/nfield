/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorOne

/-!
# Radical scaling of the actual primitive conductor rows

Only squarefree Mobius divisors contribute. Removing the repeated prime
factors scales the remainder row after division of the address, and the
constant term cancels in the nontrivial Mobius sum.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRadicalRows

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionCylinderMeans CollisionMassInverse

def conductorRadical (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

theorem conductorRadical_pos (q : ℕ) : 0 < conductorRadical q := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

theorem conductorRadical_dvd (q : ℕ) : conductorRadical q ∣ q := q.prod_primeFactors_dvd

theorem squarefree_divisor_dvd_radical {q d : ℕ} (hq : 0 < q)
    (hd : Squarefree d) (hdq : d ∣ q) : d ∣ conductorRadical q := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hdq hq.ne')

theorem conductorRadical_two_le {q : ℕ} (hq : 2 ≤ q) : 2 ≤ conductorRadical q := by
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : q≠1)
  have hpr : p ∣ conductorRadical q := squarefree_divisor_dvd_radical (by omega) hp.squarefree hpd
  exact hp.two_le.trans (Nat.le_of_dvd (conductorRadical_pos q) hpr)

theorem remainder_mul_decomposition {v e : ℕ} (hv : 0 < v) (he : 0 < e) (a : ℕ) :
    a%(v*e)=v*((a/v)%e)+a%v := by
  have ha := Nat.mod_add_div a v
  have hb := congrArg (fun n : ℕ => v*n) (Nat.mod_add_div (a/v) e)
  have hx : a=(v*((a/v)%e)+a%v)+(v*e)*((a/v)/e) := by
    nlinarith
  have hlt : v*((a/v)%e)+a%v < v*e := by
    have h := Nat.mul_le_mul_left v (Nat.succ_le_of_lt (Nat.mod_lt (a/v) he))
    nlinarith [Nat.mod_lt a hv]
  calc
    a%(v*e)=((v*((a/v)%e)+a%v)+(v*e)*((a/v)/e))%(v*e) := congrArg (fun n => n%(v*e)) hx
    _ = (v*((a/v)%e)+a%v)%(v*e) := Nat.add_mul_mod_self_left _ _ _
    _ = _ := Nat.mod_eq_of_lt hlt

theorem centeredRemainder_mul_scale {v e : ℕ} (hv : 0 < v) (he : 0 < e) (a : ℕ) :
    centeredRemainder (v*e) a=(v : ℝ)*centeredRemainder e (a/v)+
      ((a%v : ℕ) : ℝ)-((v : ℝ)-1)/2 := by
  unfold centeredRemainder
  rw [remainder_mul_decomposition hv he]
  push_cast
  ring

theorem primitiveValue_mobius_quotient {q : ℕ} (hq : 0 < q) (a : ℕ) :
    primitiveValue q a=∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℝ)*centeredRemainder (q/d) a := by
  rw [primitiveValue_formula,← Nat.sum_div_divisors q
    (fun d => (ArithmeticFunction.moebius (q/d) : ℝ)*centeredRemainder d a)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne']

theorem primitiveValue_radical_sum {q : ℕ} (hq : 0 < q) (a : ℕ) :
    primitiveValue q a=∑ d ∈ (conductorRadical q).divisors,
      (ArithmeticFunction.moebius d : ℝ)*centeredRemainder (q/d) a := by
  rw [primitiveValue_mobius_quotient hq]
  symm
  apply Finset.sum_subset (Nat.divisors_subset_of_dvd hq.ne' (conductorRadical_dvd q))
  intro d hd hnot
  have hs : ¬Squarefree d := by
    intro hs
    exact hnot (Nat.mem_divisors.mpr ⟨squarefree_divisor_dvd_radical hq hs
      (Nat.dvd_of_mem_divisors hd),(conductorRadical_pos q).ne'⟩)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,Int.cast_zero,zero_mul]

theorem primitiveValue_radical_scale {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    primitiveValue q a=((q/conductorRadical q : ℕ) : ℝ)*
      primitiveValue (conductorRadical q) (a/(q/conductorRadical q)) := by
  let s := conductorRadical q
  let v := q/s
  have hs : 0 < s := conductorRadical_pos q
  have hsd : s ∣ q := conductorRadical_dvd q
  have hv : 0 < v := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < q) hsd) hs
  have hqv : v*s=q := Nat.div_mul_cancel hsd
  have hs1 : s≠1 := by have := conductorRadical_two_le hq; omega
  rw [primitiveValue_radical_sum (by omega : 0 < q) a,
    primitiveValue_mobius_quotient hs]
  change (∑ d ∈ s.divisors, (ArithmeticFunction.moebius d : ℝ)*centeredRemainder (q/d) a)=
    (v : ℝ)*∑ d ∈ s.divisors, (ArithmeticFunction.moebius d : ℝ)*centeredRemainder (s/d) (a/v)
  have ht (d : ℕ) (hd : d ∈ s.divisors) :
      (ArithmeticFunction.moebius d : ℝ)*centeredRemainder (q/d) a=
        (v : ℝ)*((ArithmeticFunction.moebius d : ℝ)*centeredRemainder (s/d) (a/v))+
        (ArithmeticFunction.moebius d : ℝ)*(((a%v : ℕ) : ℝ)-((v : ℝ)-1)/2) := by
    have hdv := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hquot : q/d=v*(s/d) := by rw [← hqv,Nat.mul_div_assoc v hdv]
    rw [hquot,centeredRemainder_mul_scale hv
      (Nat.div_pos (Nat.le_of_dvd hs hdv) hd0)]
    ring
  rw [Finset.sum_congr rfl ht,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    moebius_divisor_sum,if_neg hs1,zero_mul,add_zero]

end NField.Alignment.CollisionRadicalRows
