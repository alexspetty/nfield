/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRestrictedGap
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Exact CRT candidates for the restricted conductor gap

A prime above half the cutoff occurs in exactly one conductor row. The
other rows have a coprime common period, giving an actual interior address
with gap two thirds of the full infinite prime amplitude.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeCandidate

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionFiniteRegrouping CollisionConductorOne
open CollisionConductorExtrema CollisionOdometerRecurrence CollisionCylinderOne
open CollisionRestrictedGap
open CollisionJordanVariance

def complementPeriod (Q p : ℕ) : ℕ := ((Finset.Icc 1 Q).erase p).lcm id
def primeCandidate (Q p : ℕ) (h : (complementPeriod Q p).Coprime p) : ℕ :=
  Nat.chineseRemainder h 0 1

theorem prime_divisor_in_top_range {p d Q : ℕ} (hp : Nat.Prime p)
    (hQ : Q < 2*p) (hd : 1 ≤ d) (hdQ : d ≤ Q) (hpd : p ∣ d) : d=p := by
  obtain ⟨k,hk⟩ := hpd
  have hk0 : k ≠ 0 := by intro h; rw [h,Nat.mul_zero] at hk; omega
  have hk1 : k=1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have := hp.pos
    nlinarith
  simpa [hk1] using hk

theorem complementPeriod_pos (Q p : ℕ) : 0 < complementPeriod Q p := by
  apply Nat.pos_of_ne_zero
  rw [complementPeriod,Finset.lcm_ne_zero_iff]
  intro d hd
  have hm := Finset.mem_Icc.mp (Finset.mem_erase.mp hd).2
  change d ≠ 0
  omega

theorem dvd_complementPeriod {Q p d : ℕ} (hd : 1 ≤ d) (hdQ : d ≤ Q) (hdp : d ≠ p) :
    d ∣ complementPeriod Q p :=
  Finset.dvd_lcm (Finset.mem_erase.mpr ⟨hdp,Finset.mem_Icc.mpr ⟨hd,hdQ⟩⟩)

theorem prime_coprime_complement {Q p : ℕ} (hp : Nat.Prime p) (hQ : Q < 2*p) :
    p.Coprime (complementPeriod Q p) := by
  have hprod : p.Coprime (∏ d ∈ (Finset.Icc 1 Q).erase p, d) := by
    apply Nat.Coprime.prod_right
    intro d hd
    apply hp.coprime_iff_not_dvd.mpr
    intro hpd
    have hm := Finset.mem_erase.mp hd
    have hb := Finset.mem_Icc.mp hm.2
    exact hm.1 (prime_divisor_in_top_range hp hQ hb.1 hb.2 hpd)
  exact hprod.of_dvd_right (Finset.lcm_dvd_prod _ id)

theorem cutoffPeriod_eq_prime_mul_complement {Q p : ℕ} (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) : cutoffPeriod Q=p*complementPeriod Q p := by
  have hm : p ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨by have := hp.two_le; omega,hpQ⟩
  unfold cutoffPeriod complementPeriod
  nth_rw 1 [← Finset.insert_erase hm]
  rw [Finset.lcm_insert]
  change Nat.lcm p (((Finset.Icc 1 Q).erase p).lcm id)=p*((Finset.Icc 1 Q).erase p).lcm id
  exact (prime_coprime_complement hp hQ).lcm_eq_mul

theorem complementPeriod_eq_div {Q p : ℕ} (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) : complementPeriod Q p=cutoffPeriod Q/p := by
  rw [cutoffPeriod_eq_prime_mul_complement hp hpQ hQ,Nat.mul_div_right _ hp.pos]

theorem complementPeriod_ge_two {Q p : ℕ} (hQ : 3 ≤ Q) : 2 ≤ complementPeriod Q p := by
  by_cases hp2 : p=2
  · have hd := dvd_complementPeriod (Q := Q) (p := p) (d := 3) (by norm_num) hQ (by omega)
    have := Nat.le_of_dvd (complementPeriod_pos Q p) hd
    omega
  · exact Nat.le_of_dvd (complementPeriod_pos Q p)
      (dvd_complementPeriod (by norm_num) (by omega : 2 ≤ Q) (Ne.symm hp2))

theorem primeCandidate_mod_complement (Q p : ℕ) (h : (complementPeriod Q p).Coprime p) :
    primeCandidate Q p h % complementPeriod Q p=0 := by
  have he := (Nat.chineseRemainder h 0 1).property.1
  simpa only [Nat.ModEq,Nat.zero_mod,primeCandidate] using he

theorem primeCandidate_mod_prime {Q p : ℕ} (hp : Nat.Prime p)
    (h : (complementPeriod Q p).Coprime p) : primeCandidate Q p h % p=1 := by
  have he := (Nat.chineseRemainder h 0 1).property.2
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt,primeCandidate] using he

theorem primeCandidate_lt_period {Q p : ℕ} (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) :
    primeCandidate Q p (prime_coprime_complement hp hQ).symm < cutoffPeriod Q := by
  rw [cutoffPeriod_eq_prime_mul_complement hp hpQ hQ,mul_comm]
  exact Nat.chineseRemainder_lt_mul _ 0 1 (complementPeriod_pos Q p).ne' hp.ne_zero

theorem primeCandidate_other_remainder {Q p d : ℕ} (hd : 1 ≤ d) (hdQ : d ≤ Q)
    (hdp : d ≠ p) (h : (complementPeriod Q p).Coprime p) :
    primeCandidate Q p h % d=0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact (dvd_complementPeriod hd hdQ hdp).trans
    (Nat.dvd_of_mod_eq_zero (primeCandidate_mod_complement Q p h))

theorem primeCandidate_interior {Q p : ℕ} (hQ3 : 3 ≤ Q) (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) :
    primeCandidate Q p (prime_coprime_complement hp hQ).symm ∈ interiorResidues Q := by
  let a := primeCandidate Q p (prime_coprime_complement hp hQ).symm
  have hap : a%p=1 := primeCandidate_mod_prime hp _
  have hal : a < cutoffPeriod Q := primeCandidate_lt_period hp hpQ hQ
  have ha0 : 0 < a := by
    by_contra h
    have hz : a=0 := by omega
    simp [hz] at hap
  have hm := complementPeriod_ge_two (p := p) hQ3
  have ham : a%complementPeriod Q p=0 := primeCandidate_mod_complement Q p _
  have halast : a ≠ cutoffPeriod Q-1 := by
    intro he
    have he' : a+1=cutoffPeriod Q := by have := cutoffPeriod_pos Q; omega
    have hdiv : complementPeriod Q p ∣ a+1 := by
      rw [he',cutoffPeriod_eq_prime_mul_complement hp hpQ hQ]
      exact dvd_mul_left _ _
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    have hfalse : (1 : ℕ)=0 := by
      simpa only [Nat.add_mod,ham,zero_add,Nat.mod_eq_of_lt
        (by omega : 1 < complementPeriod Q p)] using hz
    omega
  exact interiorResidues_mem.mpr ⟨ha0,by omega⟩

theorem primeCandidate_gap {Q p : ℕ} (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) :
    conductorGap Q (primeCandidate Q p (prime_coprime_complement hp hQ).symm)=
      (2/3 : ℝ)*amplitude p := by
  rw [conductorGap_formula,Finset.sum_eq_single p]
  · rw [primeCandidate_mod_prime hp,beta_top_range hp.pos hpQ hQ]
    simp
  · intro d hd hdp
    have hm := Finset.mem_Icc.mp hd
    rw [primeCandidate_other_remainder (by omega : 1 ≤ d) hm.2 hdp]
    simp
  · intro hnot
    exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hp.two_le,hpQ⟩))

theorem restrictedGap_le_prime {Q p : ℕ} (hQ3 : 3 ≤ Q) (hp : Nat.Prime p)
    (hpQ : p ≤ Q) (hQ : Q < 2*p) : restrictedGap Q ≤ (2/3 : ℝ)*amplitude p := by
  have h := restrictedGap_le hQ3 (primeCandidate_interior hQ3 hp hpQ hQ)
  rwa [primeCandidate_gap hp hpQ hQ] at h

end NField.Alignment.CollisionPrimeCandidate
