/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTaylorBudget
import NField.Alignment.MagnitudeShortComparison

/-!
# Applying the rounded Taylor budget to prime-square character comparison

The occurrence and degree conditions determine a full multiplicative
monomial. Its unit and size conditions are derived before applying exact
orthogonality. No bound on the completed monomial is assumed.
-/

set_option autoImplicit false

namespace NField.Alignment.HarperPrimeSquareComparison

open Filter MeasureTheory
open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.SteinhausMoment
open NField.Alignment.MagnitudeShortComparison
open NField.Alignment.HarperRoundedCutoff
open NField.Alignment.HarperTaylorBudget

/-- Complete Taylor products are positive units and strictly below p squared,
eventually for every prime p, uniformly over all the indicated monomials. -/
theorem eventual_taylor_support {ι : Type*} : ∀ᶠ p : ℕ in atTop,
    ∀ (_hp : p.Prime) (n : ℕ) (s : Finset ι) (a : ι → ℕ), 0 < n →
      (n : ℝ) ≤ (p : ℝ)-1 →
      (∀ i ∈ s, 0 < a i ∧ (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      s.card ≤ factorCount ((p : ℝ)-1)*(2*taylorOrder ((p : ℝ)-1)-1) →
      0 < completeMonomial n s a ∧ completeMonomial n s a < p^2 ∧
        (completeMonomial n s a).Coprime (p^2) := by
  filter_upwards [base_minus_one_tendsto.eventually (eventual_taylor_monomial_size (ι := ι)),
    base_minus_one_tendsto.eventually eventual_cutoff_square_lt,
    eventually_ge_atTop (2 : ℕ)] with p hbound hsmall hp2
  intro hp n s a hn hnx ha hc
  have hnp : n < p := by
    have h : (n : ℝ) < p := by linarith
    exact_mod_cast h
  have hap (i : ι) (hi : i ∈ s) : a i < p := by
    have h : (a i : ℝ) < p := by linarith [(ha i hi).2]
    exact_mod_cast h
  have hpos : 0 < completeMonomial n s a :=
    Nat.mul_pos hn (Finset.prod_pos (fun i hi => (ha i hi).1))
  have hsize := (hbound n s a hnx (fun i hi => (ha i hi).2) hc)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hR : (completeMonomial n s a : ℝ) < (p : ℝ)^2 :=
    ((hsize.1.trans_lt hsize.2.1).trans hsize.2.2).trans (by nlinarith)
  have hunit : (completeMonomial n s a).Coprime (p^2) :=
    (small_factor_unit hp hn hnp).mul_left (Nat.Coprime.prod_left
      (fun i hi => small_factor_unit hp (ha i hi).1 (hap i hi)))
  exact ⟨hpos, by exact_mod_cast hR, hunit⟩

/-- Exact comparison for the whole Taylor monomials with the eventual
size and unit checks discharged by the rounded parameter construction. -/
theorem eventual_taylor_comparison {ι κ : Type*} : ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p^2)], p.Prime →
    ∀ (n m : ℕ) (s : Finset ι) (t : Finset κ) (a : ι → ℕ) (b : κ → ℕ),
      0 < n → 0 < m → (n : ℝ) ≤ (p : ℝ)-1 → (m : ℝ) ≤ (p : ℝ)-1 →
      (∀ i ∈ s, 0 < a i ∧ (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      (∀ j ∈ t, 0 < b j ∧ (b j : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      s.card ≤ factorCount ((p : ℝ)-1)*(2*taylorOrder ((p : ℝ)-1)-1) →
      t.card ≤ factorCount ((p : ℝ)-1)*(2*taylorOrder ((p : ℝ)-1)-1) →
      fullCharacterAverage (fun χ : Character (p^2) =>
        (χ (n : ZMod (p^2))*∏ i ∈ s, χ (a i : ZMod (p^2))) *
          star (χ (m : ZMod (p^2))*∏ j ∈ t, χ (b j : ZMod (p^2)))) =
      ∫ ω, (steinhaus n ω*∏ i ∈ s, steinhaus (a i) ω) *
        star (steinhaus m ω*∏ j ∈ t, steinhaus (b j) ω) ∂phaseMeasure := by
  filter_upwards [eventual_taylor_support (ι := ι), eventual_taylor_support (ι := κ)]
    with p hs ht
  intro _ hp n m s t a b hn hm hnx hmx ha hb hc hd
  have hu := hs hp n s a hn hnx ha hc
  have hv := ht hp m t b hm hmx hb hd
  have h := character_random_pair_comparison hu.1 hv.1 hu.2.1 hv.2.1 hu.2.2 hv.2.2
  simpa only [completeMonomial, Nat.cast_mul, Nat.cast_prod, map_mul, map_prod,
    steinhaus_mul, steinhaus_prod] using h

/-- Remainder pairings, uniformly for every j up to the full factor count. -/
theorem eventual_remainder_comparison {ι κ : Type*} : ∀ᶠ p : ℕ in atTop,
    ∀ [NeZero (p^2)], p.Prime →
    ∀ (j n m : ℕ) (s : Finset ι) (t : Finset κ) (a : ι → ℕ) (b : κ → ℕ),
      j ≤ factorCount ((p : ℝ)-1) →
      0 < n → 0 < m → (n : ℝ) ≤ (p : ℝ)-1 → (m : ℝ) ≤ (p : ℝ)-1 →
      (∀ i ∈ s, 0 < a i ∧ (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      (∀ k ∈ t, 0 < b k ∧ (b k : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      s.card ≤ taylorOrder ((p : ℝ)-1)*j →
      t.card ≤ taylorOrder ((p : ℝ)-1)*j →
      fullCharacterAverage (fun χ : Character (p^2) =>
        (χ (n : ZMod (p^2))*∏ i ∈ s, χ (a i : ZMod (p^2))) *
          star (χ (m : ZMod (p^2))*∏ k ∈ t, χ (b k : ZMod (p^2)))) =
      ∫ ω, (steinhaus n ω*∏ i ∈ s, steinhaus (a i) ω) *
        star (steinhaus m ω*∏ k ∈ t, steinhaus (b k) ω) ∂phaseMeasure := by
  filter_upwards [eventual_taylor_comparison (ι := ι) (κ := κ),
    base_minus_one_tendsto.eventually eventual_taylor_data] with p hcomp hdata
  intro _ hp j n m s t a b hj hn hm hnx hmx ha hb hs ht
  have hdeg : taylorOrder ((p : ℝ)-1) ≤ 2*taylorOrder ((p : ℝ)-1)-1 := by
    have h := hdata.2.2.1
    omega
  have hbound : taylorOrder ((p : ℝ)-1)*j ≤
      factorCount ((p : ℝ)-1)*(2*taylorOrder ((p : ℝ)-1)-1) := by
    calc
      _ ≤ taylorOrder ((p : ℝ)-1)*factorCount ((p : ℝ)-1) := Nat.mul_le_mul_left _ hj
      _ = factorCount ((p : ℝ)-1)*taylorOrder ((p : ℝ)-1) := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hdeg
  exact hcomp hp n m s t a b hn hm hnx hmx ha hb (hs.trans hbound) (ht.trans hbound)

end NField.Alignment.HarperPrimeSquareComparison
