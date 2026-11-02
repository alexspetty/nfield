/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeSeparation
import NField.Alignment.KorolevLargeSquares
import Mathlib.Data.Nat.Squarefree

/-!
# Literal squarefree representation outside the actual exception set

A positive integer outside the large-square and two missing-prime sets
has n=l^2*p*q*h with small l and squarefree p*q*h. The selected primes
are identified by their real endpoint inequalities, including the
contiguous family's individual interval index.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSquarefreeRepresentation
open KorolevLargeSquares KorolevMissingPrimeCount KorolevPrimeWindows
open scoped Classical

def exceptionSet (x : ℝ) (P Q : Finset ℕ) : Finset ℕ :=
  largeSquareSet x (Real.log x) ∪ avoidSet x P ∪ avoidSet x Q

def HasSelectedRepresentation (x : ℝ) (P Q : Finset ℕ) (n : ℕ) : Prop :=
  ∃ l p q h : ℕ, 0 < l ∧ (l : ℝ) ≤ Real.log x ∧ 0 < h ∧
    p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∈ P ∧ q ∈ Q ∧
    n = l^2*p*q*h ∧ Squarefree (p*q*h)

theorem representation_outside_exception {x : ℝ} (hx : 0 ≤ x) {P Q : Finset ℕ}
    (hprimes : ∀ p ∈ P, ∀ q ∈ Q, p.Prime ∧ q.Prime ∧ Real.log x < (q : ℝ) ∧ q < p)
    {n : ℕ} (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (hout : n ∉ exceptionSet x P Q) :
    HasSelectedRepresentation x P Q n := by
  simp only [exceptionSet, Finset.mem_union, not_or] at hout
  have hP : ∃ p ∈ P, p ∣ n := by
    by_contra hh
    push Not at hh
    exact hout.1.2 ((avoidSet_mem hx P n).mpr ⟨hn, hnx, hh⟩)
  have hQ : ∃ q ∈ Q, q ∣ n := by
    by_contra hh
    push Not at hh
    exact hout.2 ((avoidSet_mem hx Q n).mpr ⟨hn, hnx, hh⟩)
  obtain ⟨p, hp, hpn⟩ := hP
  obtain ⟨q, hq, hqn⟩ := hQ
  obtain ⟨hpp, hqp, hqlarge, hqporder⟩ := hprimes p hp q hq
  obtain ⟨b, l, hb, hl, hln, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hlbound : (l : ℝ) ≤ Real.log x := by
    by_contra hh
    exact hout.1.1 ((largeSquareSet_mem hx (Real.log x) n).mpr
      ⟨hn, hnx, l, lt_of_not_ge hh, ⟨b, hln.symm⟩⟩)
  have hpnl : ¬p ∣ l := by
    intro h
    have hh : (p : ℝ) ≤ l := by exact_mod_cast Nat.le_of_dvd hl h
    have hqpR : (q : ℝ) < p := by exact_mod_cast hqporder
    linarith
  have hqnl : ¬q ∣ l := by
    intro h
    have hh : (q : ℝ) ≤ l := by exact_mod_cast Nat.le_of_dvd hl h
    linarith
  have hpb : p ∣ b := by
    rw [← hln] at hpn
    exact (hpp.dvd_mul.mp hpn).resolve_left (fun h => hpnl (hpp.dvd_of_dvd_pow h))
  have hqb : q ∣ b := by
    rw [← hln] at hqn
    exact (hqp.dvd_mul.mp hqn).resolve_left (fun h => hqnl (hqp.dvd_of_dvd_pow h))
  have hpq : p ≠ q := hqporder.ne'
  have hd := ((Nat.coprime_primes hpp hqp).mpr hpq).mul_dvd_of_dvd_of_dvd hpb hqb
  obtain ⟨h, hbh⟩ := hd
  have hh : 0 < h := by
    by_contra hh
    have hz : h = 0 := by omega
    simp [hz] at hbh
    omega
  refine ⟨l, p, q, h, hl, hlbound, hh, hpp, hqp, hpq, hp, hq, ?_, ?_⟩
  · rw [← hln, hbh]
    ring
  · rwa [hbh] at hsf

theorem exception_count_le (x : ℝ) (P Q : Finset ℕ) (m : ℕ) :
    (((exceptionSet x P Q).filter (fun n => n.Coprime m)).card : ℝ) ≤
      (((largeSquareSet x (Real.log x)).filter (fun n => n.Coprime m)).card : ℝ) +
      (((avoidSet x P).filter (fun n => n.Coprime m)).card : ℝ) +
      (((avoidSet x Q).filter (fun n => n.Coprime m)).card : ℝ) := by
  rw [exceptionSet, Finset.filter_union, Finset.filter_union]
  exact_mod_cast (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

theorem contiguous_interval_membership {L : ℝ} (hL : 0 ≤ L) {a b q : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    q ∈ KorolevPrimeIntervals.intervalPrimes (upperEndpoint L (b+1)) (upperEndpoint L a) ↔
      ∃ s : ℕ, a ≤ s ∧ s ≤ b ∧ q.Prime ∧
        upperEndpoint L (s+1) < (q : ℝ) ∧ (q : ℝ) ≤ upperEndpoint L s := by
  constructor
  · intro hq
    obtain ⟨hqp, hlo, hhi⟩ := KorolevPrimeIntervals.intervalPrimes_mem.mp hq
    let S := (Finset.Icc a b).filter (fun s => (q : ℝ) ≤ upperEndpoint L s)
    have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hab⟩, hhi⟩
    have hne : S.Nonempty := ⟨a, haS⟩
    let s := S.max' hne
    have hs : s ∈ S := Finset.max'_mem S hne
    obtain ⟨hsab, hqs⟩ := Finset.mem_filter.mp hs
    obtain ⟨has, hsb⟩ := Finset.mem_Icc.mp hsab
    refine ⟨s, has, hsb, hqp, ?_, hqs⟩
    by_cases hsb' : s = b
    · simpa [hsb'] using hlo
    · apply lt_of_not_ge
      intro hh
      have hs' : s+1 ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hh⟩
      have hmax := Finset.le_max' S (s+1) hs'
      change s+1 ≤ s at hmax
      omega
  · rintro ⟨s, has, hsb, hqp, hlo, hhi⟩
    apply KorolevPrimeIntervals.intervalPrimes_mem.mpr
    refine ⟨hqp, ?_, ?_⟩
    · exact lt_of_le_of_lt (upper_antitone hL (by omega : 1 ≤ s+1) (by omega : s+1 ≤ b+1)) hlo
    · exact hhi.trans (upper_antitone hL ha has)

end NField.Alignment.KorolevSquarefreeRepresentation
