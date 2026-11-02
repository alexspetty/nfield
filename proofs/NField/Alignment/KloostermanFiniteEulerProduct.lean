/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanSiftedSeries
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# A finite Euler product through every requested degree

The product ranges over all actual monic irreducibles of degree at most N.
Multiplying the actual L-series by these Euler factors leaves constant
coefficient one and zero coefficients in degrees 1 through N. This is the
coefficientwise Euler product, with no analytic convergence hypothesis.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanFiniteEulerProduct
open scoped BigOperators Classical
open Polynomial KloostermanMonicCoefficients KloostermanPolynomialCharacter
  KloostermanSiftedSeries KloostermanQuadraticLSeries

noncomputable def boundedMonicPolynomials (p : ℕ) [Fact p.Prime]
    (N : ℕ) : Finset (ZMod p)[X] :=
  (Finset.range (N+1)).biUnion fun n =>
    (Finset.univ : Finset (MonicDegree (ZMod p) n)).image Subtype.val

theorem mem_boundedMonicPolynomials (p : ℕ) [Fact p.Prime]
    (N : ℕ) (f : (ZMod p)[X]) :
    f ∈ boundedMonicPolynomials p N ↔ f.Monic ∧ f.natDegree ≤ N := by
  simp only [boundedMonicPolynomials,Finset.mem_biUnion,Finset.mem_range,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨n,hn,g,rfl⟩
    exact ⟨g.property.1,by rw [g.property.2]; omega⟩
  · rintro ⟨hf,hd⟩
    exact ⟨f.natDegree,by omega,⟨f,hf,rfl⟩,rfl⟩

noncomputable def boundedIrreducibles (p : ℕ) [Fact p.Prime]
    (N : ℕ) : Finset (ZMod p)[X] :=
  (boundedMonicPolynomials p N).filter Irreducible

theorem mem_boundedIrreducibles (p : ℕ) [Fact p.Prime]
    (N : ℕ) (f : (ZMod p)[X]) :
    f ∈ boundedIrreducibles p N ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ≤ N := by
  simp only [boundedIrreducibles,Finset.mem_filter,mem_boundedMonicPolynomials]
  tauto

theorem boundedIrreducibles_properties (p : ℕ) [Fact p.Prime]
    (N : ℕ) : ∀ f ∈ boundedIrreducibles p N, f.Monic ∧ Irreducible f := by
  intro f hf
  have h := (mem_boundedIrreducibles p N f).mp hf
  exact ⟨h.1,h.2.1⟩

/-- Every nonconstant monic polynomial in the requested degree range has
an actual irreducible divisor included in the finite product. -/
theorem not_avoids_boundedIrreducibles (p : ℕ) [Fact p.Prime]
    (N n : ℕ) (hn : 0<n) (hN : n≤N) (f : MonicDegree (ZMod p) n) :
    ¬ Avoids (boundedIrreducibles p N) f.val := by
  intro h
  have hu : ¬ IsUnit f.val := by
    intro hu
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [f.property.2] at hd
    omega
  obtain ⟨g,hg,hi,hd⟩ := Polynomial.exists_monic_irreducible_factor f.val hu
  have hdeg : g.natDegree ≤ N := by
    have he := Polynomial.natDegree_le_of_dvd hd f.property.1.ne_zero
    rw [f.property.2] at he
    omega
  exact h g ((mem_boundedIrreducibles p N g).mpr ⟨hg,hi,hdeg⟩) hd

/-- Sieving by nonunits leaves the constant monic polynomial one. -/
theorem siftedCoefficient_zero (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X])
    (hs : ∀ g ∈ s, Irreducible g) : siftedCoefficient p a b m s 0 = 1 := by
  have hsame : siftedCoefficient p a b m s 0 = degreeCoefficient p a b m 0 := by
    unfold siftedCoefficient degreeCoefficient
    apply Finset.sum_congr rfl
    intro f _
    have hf : f.val=1 := Polynomial.eq_one_of_monic_natDegree_zero
      f.property.1 f.property.2
    have ha : Avoids s f.val := by
      intro g hg hd
      rw [hf] at hd
      exact (hs g hg).not_isUnit (isUnit_of_dvd_one hd)
    rw [if_pos ha]
  rw [hsame,degreeCoefficient_zero]

theorem siftedCoefficient_bounded_eq_zero (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N n : ℕ) (hn : 0<n) (hN : n≤N) :
    siftedCoefficient p a b m (boundedIrreducibles p N) n = 0 := by
  unfold siftedCoefficient
  apply Finset.sum_eq_zero
  intro f _
  exact if_neg (not_avoids_boundedIrreducibles p N n hn hN f)

noncomputable def finiteEulerDenominator (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N : ℕ) : PowerSeries ℂ :=
  ∏ g ∈ boundedIrreducibles p N, eulerFactor p a b m g

/-- Actual finite Euler-product identity in every coefficient up to N.
The prime polynomial X, including its zero character, is included. -/
theorem coeff_finiteEulerDenominator_mul_LSeries (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N n : ℕ) (hn : n≤N) :
    PowerSeries.coeff n
      (finiteEulerDenominator p a b m N * formalLSeries p a b m) =
        if n=0 then 1 else 0 := by
  rw [finiteEulerDenominator, ← siftedSeries_eq_finite_product p a b m _
    (boundedIrreducibles_properties p N), siftedSeries, PowerSeries.coeff_mk]
  by_cases h0 : n=0
  · subst n
    rw [if_pos rfl]
    exact siftedCoefficient_zero p a b m _
      (fun g hg => (boundedIrreducibles_properties p N g hg).2)
  · rw [if_neg h0]
    exact siftedCoefficient_bounded_eq_zero p a b m N n (by omega) hn

/-- Equivalent polynomial-truncation form of the finite Euler identity. -/
theorem trunc_finiteEulerDenominator_mul_LSeries (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N : ℕ) :
    PowerSeries.trunc (N+1)
      (finiteEulerDenominator p a b m N * formalLSeries p a b m) = 1 := by
  ext n
  rw [PowerSeries.coeff_trunc,Polynomial.coeff_one]
  by_cases hn : n<N+1
  · rw [if_pos hn, coeff_finiteEulerDenominator_mul_LSeries p a b m N n (by omega)]
  · rw [if_neg hn,if_neg (by omega : n≠0)]

end NField.Alignment.KloostermanFiniteEulerProduct
