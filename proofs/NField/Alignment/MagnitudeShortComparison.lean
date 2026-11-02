/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudePolynomialMoment
import NField.Alignment.SteinhausMoment

/-!
# Exact character-to-Steinhaus comparison below the modulus

The mean uses every Dirichlet character and its actual totient normalization.
Positive unit indices strictly below the modulus make residue equality literal
integer equality. The random side is the concrete infinite Haar-product model,
not an orthogonality hypothesis. Finite weighted extensions keep restrictions
on the complete indices of each pairing.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeShortComparison

open scoped BigOperators ComplexConjugate ZMod
open MeasureTheory
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.MagnitudePolynomialMoment
open NField.Alignment.SteinhausMoment
open NField.Alignment.SpectralRepulsion

noncomputable def fullCharacterAverage {q : ℕ} [NeZero q]
    (F : Character q → ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ χ : Character q, F χ

/-- The full population mean has precisely the displayed totient denominator. -/
theorem full_character_average {q : ℕ} [NeZero q] (F : Character q → ℂ) :
    fullCharacterAverage F = (1 / (q.totient : ℂ)) * ∑ χ : Character q, F χ ∧
      fullCharacterAverage F =
        (Fintype.card (Character q) : ℂ)⁻¹ * ∑ χ : Character q, F χ := by
  simp only [one_div, character_card_eq_totient, fullCharacterAverage, and_self]

theorem full_character_average_real {q : ℕ} [NeZero q] (F : Character q → ℝ) :
    fullCharacterAverage (fun χ => (F χ : ℂ)) = (uniformAverage F : ℂ) := by
  simp only [fullCharacterAverage, uniformAverage, character_card_eq_totient,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]

theorem short_character_orthogonality {q u v : ℕ} [NeZero q]
    (huq : u<q) (hvq : v<q) (hv : v.Coprime q) :
    fullCharacterAverage (fun χ : Character q => χ (u : ZMod q) *
      star (χ (v : ZMod q))) = if u=v then 1 else 0 := by
  classical
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum : (∑ χ : Character q, χ (u : ZMod q) * star (χ (v : ZMod q))) =
      if u=v then (q.totient : ℂ) else 0 := by
    calc
      _ = ∑ χ : Character q, star (χ (v : ZMod q)) * χ (u : ZMod q) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = _ := by
        rw [residue_character_orthogonality]
        have hiff : v%q=u%q ∧ v.Coprime q ↔ u=v := by
          rw [Nat.mod_eq_of_lt hvq, Nat.mod_eq_of_lt huq]
          exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, hv⟩⟩
        simp only [hiff]
  unfold fullCharacterAverage
  rw [hsum]
  split_ifs <;> simp [hφ]

/-- Both equalities in the manuscript's `eq:short-orthogonality`. -/
theorem short_orthogonality {q u v : ℕ} [NeZero q]
    (hu : 0<u) (hv : 0<v) (huq : u<q) (hvq : v<q)
    (_huc : u.Coprime q) (hvc : v.Coprime q) :
    fullCharacterAverage (fun χ : Character q => χ (u : ZMod q) *
      star (χ (v : ZMod q))) = (if u=v then 1 else 0) ∧
      (if u=v then (1 : ℂ) else 0) =
        ∫ ω, steinhaus u ω * star (steinhaus v ω) ∂phaseMeasure := by
  exact ⟨short_character_orthogonality huq hvq hvc,
    (steinhaus_orthogonality hu.ne' hv.ne').symm⟩

theorem character_random_pair_comparison {q u v : ℕ} [NeZero q]
    (hu : 0<u) (hv : 0<v) (huq : u<q) (hvq : v<q)
    (huc : u.Coprime q) (hvc : v.Coprime q) :
    fullCharacterAverage (fun χ : Character q => χ (u : ZMod q) *
      star (χ (v : ZMod q))) =
        ∫ ω, steinhaus u ω * star (steinhaus v ω) ∂phaseMeasure :=
  (short_orthogonality hu hv huq hvq huc hvc).1.trans
    (short_orthogonality hu hv huq hvq huc hvc).2

theorem fullCharacterAverage_sum {q : ℕ} [NeZero q] {ι : Type*}
    (s : Finset ι) (F : ι → Character q → ℂ) :
    fullCharacterAverage (fun χ => ∑ i ∈ s, F i χ) =
      ∑ i ∈ s, fullCharacterAverage (F i) := by
  unfold fullCharacterAverage
  rw [Finset.sum_comm, Finset.mul_sum]

theorem fullCharacterAverage_const_mul {q : ℕ} [NeZero q]
    (c : ℂ) (F : Character q → ℂ) :
    fullCharacterAverage (fun χ => c * F χ) = c * fullCharacterAverage F := by
  unfold fullCharacterAverage
  rw [← Finset.mul_sum]
  ring

/-- Termwise comparison for arbitrary complex weights on complete products. -/
theorem finite_pairing_comparison {q : ℕ} [NeZero q]
    (s t : Finset ℕ) (c : ℕ → ℕ → ℂ)
    (hs : ∀ u ∈ s, 0<u ∧ u<q ∧ u.Coprime q)
    (ht : ∀ v ∈ t, 0<v ∧ v<q ∧ v.Coprime q) :
    fullCharacterAverage (fun χ : Character q => ∑ u ∈ s, ∑ v ∈ t,
      c u v * (χ (u : ZMod q) * star (χ (v : ZMod q)))) =
      ∫ ω, ∑ u ∈ s, ∑ v ∈ t,
        c u v * (steinhaus u ω * star (steinhaus v ω)) ∂phaseMeasure := by
  rw [finite_pairing_integral s t c (fun u hu => (hs u hu).1.ne')
    (fun v hv => (ht v hv).1.ne')]
  rw [fullCharacterAverage_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [fullCharacterAverage_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [fullCharacterAverage_const_mul,
    short_character_orthogonality (hs u hu).2.1 (ht v hv).2.1 (ht v hv).2.2]

theorem character_polynomial_pair_expansion {q : ℕ} [NeZero q]
    (s t : Finset ℕ) (c d : ℕ → ℂ) (χ : Character q) :
    (∑ u ∈ s, c u * χ (u : ZMod q)) * star (∑ v ∈ t, d v * χ (v : ZMod q)) =
      ∑ u ∈ s, ∑ v ∈ t, (c u * star (d v)) *
        (χ (u : ZMod q) * star (χ (v : ZMod q))) := by
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact mixed second moments for finite polynomials supported on positive
units below the modulus. Coefficients may be complex. -/
theorem polynomial_pair_comparison {q : ℕ} [NeZero q]
    (s t : Finset ℕ) (c d : ℕ → ℂ)
    (hs : ∀ u ∈ s, 0<u ∧ u<q ∧ u.Coprime q)
    (ht : ∀ v ∈ t, 0<v ∧ v<q ∧ v.Coprime q) :
    fullCharacterAverage (fun χ : Character q =>
      (∑ u ∈ s, c u * χ (u : ZMod q)) *
        star (∑ v ∈ t, d v * χ (v : ZMod q))) =
      ∫ ω, (∑ u ∈ s, c u * steinhaus u ω) *
        star (∑ v ∈ t, d v * steinhaus v ω) ∂phaseMeasure := by
  simp_rw [character_polynomial_pair_expansion, polynomial_pair_expansion]
  exact finite_pairing_comparison s t _ hs ht

/-- Equality of the actual real second moments, with arbitrary complex weights. -/
theorem polynomial_second_moment_comparison {q : ℕ} [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℂ)
    (hs : ∀ u ∈ s, 0<u ∧ u<q ∧ u.Coprime q) :
    uniformAverage (fun χ : Character q => ‖∑ u ∈ s, c u * χ (u : ZMod q)‖^2) =
      ∫ ω, ‖∑ u ∈ s, c u * steinhaus u ω‖^2 ∂phaseMeasure := by
  have h := polynomial_pair_comparison s s c c hs hs
  simp_rw [self_pair_eq_norm_sq, full_character_average_real] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem small_factor_unit {p n : ℕ} (hp : p.Prime) (hn : 0<n) (hnp : n<p) :
    n.Coprime (p^2) :=
  hp.coprime_pow_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn hnp)

/-- Powers of every positive factor below p remain units modulo p squared. -/
theorem powered_product_unit {ι : Type*} {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (a e : ι → ℕ) (ha : ∀ i ∈ s, 0<a i ∧ a i<p) :
    (∏ i ∈ s, (a i)^(e i)).Coprime (p^2) :=
  Nat.Coprime.prod_left (fun i hi =>
    (small_factor_unit hp (ha i hi).1 (ha i hi).2).pow_left (e i))

theorem complete_product_support {ι : Type*} {p n : ℕ} (hp : p.Prime)
    (hn : 0<n) (hnp : n<p) (s : Finset ι) (a e : ι → ℕ)
    (ha : ∀ i ∈ s, 0<a i ∧ a i<p)
    (hsize : n*(∏ i ∈ s, (a i)^(e i)) < p^2) :
    0 < n*(∏ i ∈ s, (a i)^(e i)) ∧
      n*(∏ i ∈ s, (a i)^(e i)) < p^2 ∧
      (n*(∏ i ∈ s, (a i)^(e i))).Coprime (p^2) := by
  exact ⟨Nat.mul_pos hn (Finset.prod_pos (fun i hi => pow_pos (ha i hi).1 _)), hsize,
    (small_factor_unit hp hn hnp).mul_left (powered_product_unit hp s a e ha)⟩

/-- The exact comparison with the size test on each entire monomial, across
all partition factors. Bounds on individual factors alone do not suffice. -/
theorem complete_product_pair_comparison {ι κ : Type*} {p n m : ℕ}
    [NeZero (p^2)] (hp : p.Prime)
    (hn : 0 < n) (hnp : n < p) (hm : 0 < m) (hmp : m < p)
    (s : Finset ι) (t : Finset κ) (a e : ι → ℕ) (b d : κ → ℕ)
    (ha : ∀ i ∈ s, 0<a i ∧ a i<p) (hb : ∀ j ∈ t, 0<b j ∧ b j<p)
    (hu : n*(∏ i ∈ s, (a i)^(e i)) < p^2)
    (hv : m*(∏ j ∈ t, (b j)^(d j)) < p^2) :
    fullCharacterAverage (fun χ : Character (p^2) =>
      (χ (n : ZMod (p^2)) * ∏ i ∈ s, χ (a i : ZMod (p^2))^(e i)) *
        star (χ (m : ZMod (p^2)) * ∏ j ∈ t, χ (b j : ZMod (p^2))^(d j))) =
      ∫ ω, (steinhaus n ω * ∏ i ∈ s, steinhaus (a i) ω ^ (e i)) *
        star (steinhaus m ω * ∏ j ∈ t, steinhaus (b j) ω ^ (d j)) ∂phaseMeasure := by
  have hsu := complete_product_support hp hn hnp s a e ha hu
  have hsv := complete_product_support hp hm hmp t b d hb hv
  have h := character_random_pair_comparison hsu.1 hsv.1 hsu.2.1 hsv.2.1
    hsu.2.2 hsv.2.2
  simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, map_mul, map_prod, map_pow,
    steinhaus_mul, steinhaus_prod, steinhaus_pow] using h

end NField.Alignment.MagnitudeShortComparison
