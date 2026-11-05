/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCandidateScale
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Eventual classification of the restricted conductor minimizers

The scale separation forces prime-power saturation. An interior minimizer
must then miss a prime in the top half of the cutoff. Positivity of every
regrouped coefficient forces its single remainder to be one, with all
other remainders zero. The coefficients are the full infinite amplitudes.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMinimizerClassification

open scoped BigOperators Classical
open Filter
open CollisionCandidateScale CollisionConductorCosts CollisionPrimeCandidate
open CollisionRestrictedGap CollisionConductorExtrema CollisionFiniteRegrouping
open CollisionOdometerRecurrence CollisionJordanVariance

theorem prime_power_saturation {p Q a : ℕ} (hp : p.Prime) (hpa : p ∣ a)
    (hstep : ∀ j : ℕ, 1 ≤ j → p^(j+1) ≤ Q → p^j ∣ a → p^(j+1) ∣ a) :
    ∀ j : ℕ, p^j ≤ Q → p^j ∣ a := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hpQ
    by_cases hj : j=0
    · simpa [hj] using hpa
    apply hstep j (by omega) hpQ
    exact ih ((Nat.pow_le_pow_right hp.pos (Nat.le_succ j)).trans hpQ)

theorem cutoffPeriod_dvd_of_saturated {Q a : ℕ}
    (hbase : ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ a)
    (hstep : ∀ p j : ℕ, p.Prime → 1 ≤ j → p^(j+1) ≤ Q → p^j ∣ a → p^(j+1) ∣ a) :
    cutoffPeriod Q ∣ a := by
  apply (cutoffPeriod_dvd_iff Q a).mpr
  intro d hd
  have hdb := Finset.mem_Icc.mp hd
  apply (Nat.dvd_iff_prime_pow_dvd_dvd a d).mpr
  intro p j hp hpjd
  by_cases hj : j=0
  · simp [hj]
  have hpjQ : p^j ≤ Q := (Nat.le_of_dvd (by omega : 0 < d) hpjd).trans hdb.2
  have hpj : p ≤ p^j := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ j)
  exact prime_power_saturation hp (hbase p hp (hpj.trans hpjQ)) (hstep p · hp) j hpjQ

theorem interior_missing_prime {Q a : ℕ} (ha : a ∈ interiorResidues Q)
    (hstep : ∀ p j : ℕ, p.Prime → 1 ≤ j → p^(j+1) ≤ Q → p^j ∣ a → p^(j+1) ∣ a) :
    ∃ p : ℕ, p.Prime ∧ p ≤ Q ∧ ¬p ∣ a := by
  by_contra h
  push Not at h
  have hdiv := cutoffPeriod_dvd_of_saturated h hstep
  have hab := interiorResidues_mem.mp ha
  have hle := Nat.le_of_dvd hab.1 hdiv
  omega

theorem minimizer_top_prime_remainder {Q a p : ℕ} (hQ : 3 ≤ Q) (hp : p.Prime)
    (hpQ : p ≤ Q) (htop : Q < 2*p) (ha : conductorGap Q a=restrictedGap Q)
    (hmiss : ¬p ∣ a) : a%p=1 ∧ conductorGap Q a=(2/3 : ℝ)*amplitude p := by
  have hupper := restrictedGap_le_prime hQ hp hpQ htop
  have hrow := conductorGap_row_lower (a := a) hp.two_le hpQ
  rw [beta_top_range hp.pos hpQ htop] at hrow
  have hbeta := beta_pos hp.two_le hpQ
  rw [beta_top_range hp.pos hpQ htop] at hbeta
  have hrpos : 1 ≤ a%p := by
    by_contra h
    exact hmiss (Nat.dvd_of_mod_eq_zero (by omega))
  have hrle : ((a%p : ℕ) : ℝ) ≤ 1 := by
    rw [ha] at hrow
    nlinarith
  have hr : a%p=1 := by
    have hrle' : a%p ≤ 1 := by exact_mod_cast hrle
    omega
  refine ⟨hr,?_⟩
  rw [hr,Nat.cast_one,mul_one] at hrow
  rw [ha]
  exact le_antisymm hupper (by rwa [← ha])

theorem minimizer_other_remainders {Q a p : ℕ} (hQ : 3 ≤ Q) (hp : p.Prime)
    (hpQ : p ≤ Q) (htop : Q < 2*p) (ha : conductorGap Q a=restrictedGap Q)
    (hmiss : ¬p ∣ a) : ∀ d ∈ Finset.Icc 2 Q, d ≠ p → a%d=0 := by
  obtain ⟨hr,hvalue⟩ := minimizer_top_prime_remainder hQ hp hpQ htop ha hmiss
  have hpI : p ∈ Finset.Icc 2 Q := Finset.mem_Icc.mpr ⟨hp.two_le,hpQ⟩
  have hsum := conductorGap_formula Q a
  rw [← Finset.sum_erase_add _ _ hpI] at hsum
  rw [hr,Nat.cast_one,mul_one,beta_top_range hp.pos hpQ htop,hvalue] at hsum
  have hzero : (∑ d ∈ (Finset.Icc 2 Q).erase p, beta d Q*((a%d : ℕ) : ℝ))=0 := by
    linarith
  have hn : ∀ d ∈ (Finset.Icc 2 Q).erase p, 0 ≤ beta d Q*((a%d : ℕ) : ℝ) := by
    intro d hd
    have hb := Finset.mem_Icc.mp (Finset.mem_erase.mp hd).2
    exact mul_nonneg (beta_pos hb.1 hb.2).le (Nat.cast_nonneg _)
  intro d hd hdp
  have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hzero d (Finset.mem_erase.mpr ⟨hdp,hd⟩)
  have hz := (mul_eq_zero.mp he).resolve_left
    (beta_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2).ne'
  exact_mod_cast hz

theorem eventual_minimizer_coordinates :
    ∀ᶠ Q : ℕ in atTop, ∀ a ∈ interiorResidues Q,
      conductorGap Q a=restrictedGap Q →
      ∃ p : ℕ, p.Prime ∧ p ≤ Q ∧ Q < 2*p ∧ a%p=1 ∧
        (∀ d ∈ Finset.Icc 2 Q, d ≠ p → a%d=0) ∧
        conductorGap Q a=(2/3 : ℝ)*amplitude p := by
  filter_upwards [eventual_minimizer_small_primes,eventual_minimizer_higher_powers,
    eventually_ge_atTop (3 : ℕ)] with Q hsmall hhigher hQ
  intro a ha hmin
  obtain ⟨p,hp,hpQ,hmiss⟩ := interior_missing_prime ha (hhigher a hmin)
  have htop : Q < 2*p := by
    by_contra h
    exact hmiss (hsmall a hmin p hp (by omega))
  obtain ⟨hr,hgap⟩ := minimizer_top_prime_remainder hQ hp hpQ htop hmin hmiss
  exact ⟨p,hp,hpQ,htop,hr,minimizer_other_remainders hQ hp hpQ htop hmin hmiss,hgap⟩

theorem primeCandidate_eq_of_remainders {Q a p : ℕ} (hp : p.Prime)
    (hpQ : p ≤ Q) (htop : Q < 2*p) (ha : a < cutoffPeriod Q) (hap : a%p=1)
    (hother : ∀ d ∈ Finset.Icc 2 Q, d ≠ p → a%d=0) :
    a=primeCandidate Q p (prime_coprime_complement hp htop).symm := by
  have hM : complementPeriod Q p ∣ a := by
    rw [complementPeriod,Finset.lcm_dvd_iff]
    intro d hd
    have hd' := Finset.mem_erase.mp hd
    have hdQ := Finset.mem_Icc.mp hd'.2
    by_cases hd1 : d=1
    · simp [hd1]
    exact Nat.dvd_of_mod_eq_zero
      (hother d (Finset.mem_Icc.mpr ⟨by omega,hdQ.2⟩) hd'.1)
  have haM : a ≡ 0 [MOD complementPeriod Q p] := by
    simpa only [Nat.ModEq,Nat.zero_mod] using Nat.mod_eq_zero_of_dvd hM
  have hap' : a ≡ 1 [MOD p] := by
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using hap
  have he := Nat.chineseRemainder_modEq_unique (prime_coprime_complement hp htop).symm haM hap'
  have hperiod : complementPeriod Q p*p=cutoffPeriod Q := by
    rw [cutoffPeriod_eq_prime_mul_complement hp hpQ htop,mul_comm]
  rw [hperiod] at he
  exact he.eq_of_lt_of_lt ha (primeCandidate_lt_period hp hpQ htop)

def topPrimes (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter (fun p => p.Prime ∧ Q < 2*p)

def topPrimeAmplitude (Q : ℕ) : ℝ :=
  if h : (topPrimes Q).Nonempty then (topPrimes Q).inf' h amplitude else 0

theorem topPrimes_mem {Q p : ℕ} :
    p ∈ topPrimes Q ↔ p.Prime ∧ p ≤ Q ∧ Q < 2*p := by
  simp only [topPrimes,Finset.mem_filter,Finset.mem_Icc]
  exact ⟨fun h => ⟨h.2.1,h.1.2,h.2.2⟩,fun h => ⟨⟨h.1.two_le,h.2.1⟩,h.1,h.2.2⟩⟩

theorem topPrimeAmplitude_le {Q p : ℕ} (hp : p ∈ topPrimes Q) :
    topPrimeAmplitude Q ≤ amplitude p := by
  rw [topPrimeAmplitude,dif_pos ⟨p,hp⟩]
  exact Finset.inf'_le amplitude hp

theorem topPrimeAmplitude_eq_of_min {Q p : ℕ} (hp : p ∈ topPrimes Q)
    (hmin : ∀ r ∈ topPrimes Q, amplitude p ≤ amplitude r) :
    topPrimeAmplitude Q=amplitude p := by
  apply le_antisymm (topPrimeAmplitude_le hp)
  rw [topPrimeAmplitude,dif_pos ⟨p,hp⟩]
  exact Finset.le_inf' _ _ hmin

theorem eventual_restricted_gap_exact :
    ∀ᶠ Q : ℕ in atTop, restrictedGap Q=(2/3 : ℝ)*topPrimeAmplitude Q := by
  filter_upwards [eventual_minimizer_coordinates,eventually_ge_atTop (3 : ℕ)] with Q hQ hQ3
  obtain ⟨a,ha,hmin⟩ := restrictedGap_attained hQ3
  obtain ⟨p,hp,hpQ,htop,_,_,hvalue⟩ := hQ a ha hmin
  have hminp : ∀ r ∈ topPrimes Q, amplitude p ≤ amplitude r := by
    intro r hr
    have hr' := topPrimes_mem.mp hr
    have hupper := restrictedGap_le_prime hQ3 hr'.1 hr'.2.1 hr'.2.2
    rw [← hmin,hvalue] at hupper
    linarith
  rw [topPrimeAmplitude_eq_of_min (topPrimes_mem.mpr ⟨hp,hpQ,htop⟩) hminp,← hvalue,hmin]

theorem eventual_minimizer_iff_primeCandidate :
    ∀ᶠ Q : ℕ in atTop, ∀ a ∈ interiorResidues Q,
      conductorGap Q a=restrictedGap Q ↔
      ∃ p : ℕ, ∃ hp : p.Prime, ∃ _ : p ≤ Q, ∃ htop : Q < 2*p,
        amplitude p=topPrimeAmplitude Q ∧
        a=primeCandidate Q p (prime_coprime_complement hp htop).symm := by
  filter_upwards [eventual_minimizer_coordinates,eventual_restricted_gap_exact] with Q hQ hgap
  intro a ha
  constructor
  · intro hmin
    obtain ⟨p,hp,hpQ,htop,hr,hother,hvalue⟩ := hQ a ha hmin
    have hap : a < cutoffPeriod Q := by have := interiorResidues_mem.mp ha; omega
    refine ⟨p,hp,hpQ,htop,?_,primeCandidate_eq_of_remainders hp hpQ htop hap hr hother⟩
    rw [hmin,hgap] at hvalue
    linarith
  · rintro ⟨p,hp,hpQ,htop,hmin,rfl⟩
    rw [primeCandidate_gap hp hpQ htop,hmin,hgap]

end NField.Alignment.CollisionMinimizerClassification
