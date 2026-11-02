/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentPrimeLogSum

/-!
# The infinite alignment Euler product with a uniform error

The actual arithmetic jet has an absolutely convergent Euler product.
Its mass projection and convergent prime logarithmic sum determine the
first moment by the finite product formula and uniqueness of limits.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentEulerProduct

open scoped Classical
open Filter TrivSqZeroExt CollisionFiniteEulerMoments CollisionAlignmentEulerJet
open CollisionAlignmentEulerLocalSums CollisionAlignmentPrimeLogSum
open CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds
open CollisionHarmonicLocalExpansion CollisionHarmonicObservableApproximation
open CollisionCylinderMeans CollisionZetaMoments CollisionConductorArithmetic

def alignmentEulerProduct (L : ℕ) : ℝ :=
  ∏' p : Nat.Primes, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val)

theorem alignmentEulerMass_hasProd {L : ℕ} (hL : 0 < L) :
    HasProd (fun p : Nat.Primes => alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
      (alignmentEulerMass L) := by
  have h := (alignment_local_euler_hasProd hL).map (TrivSqZeroExt.fstHom ℝ ℝ ℝ)
    TrivSqZeroExt.continuous_fst
  change HasProd (fun p : Nat.Primes => alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
    (alignmentEulerMass L) at h
  exact h

theorem alignmentEulerProduct_eq_mass {L : ℕ} (hL : 0 < L) :
    alignmentEulerProduct L=alignmentEulerMass L := (alignmentEulerMass_hasProd hL).tprod_eq

theorem alignment_finite_euler_product (L : ℕ) (s : Finset Nat.Primes) :
    (∏ p ∈ s, massMoment (alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
      (alignmentPrimeNumerator (p.val : ℝ) (L.factorization p.val)*Real.log p.val))=
    massMoment (∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
      ((∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))*
        (∑ p ∈ s, alignmentPrimeLogTerm L p)) := by
  have ha (p : Nat.Primes) (hp : p ∈ s) :
      alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val) ≠ 0 := by
    have hp1 : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (alignmentPrimeFactor_bounds hp1 _).1)
  rw [dual_product_mass_moment s _ _ ha]
  apply TrivSqZeroExt.ext
  · rfl
  · change (∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))*
      (∑ p ∈ s, (alignmentPrimeNumerator (p.val : ℝ) (L.factorization p.val)*Real.log p.val)/
        alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))=_
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    unfold alignmentPrimeLogTerm alignmentPrimeAverage
    ring

theorem alignment_normalized_euler_hasProd {L : ℕ} (hL : 0 < L) :
    HasProd (fun p : Nat.Primes =>
      massMoment (alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
        (alignmentPrimeNumerator (p.val : ℝ) (L.factorization p.val)*Real.log p.val))
      (massMoment (alignmentEulerMass L) (alignmentEulerMass L*alignmentEulerLogSum L)) := by
  have hP : Tendsto
      (fun s : Finset Nat.Primes => ∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
      atTop (nhds (alignmentEulerMass L)) := alignmentEulerMass_hasProd hL
  have hS : Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, alignmentPrimeLogTerm L p)
      atTop (nhds (alignmentEulerLogSum L)) := alignmentEulerLogSum_hasSum L
  have hlim : Tendsto (fun s : Finset Nat.Primes =>
      massMoment (∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
        ((∏ p ∈ s, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))*
          (∑ p ∈ s, alignmentPrimeLogTerm L p))) atTop
      (nhds (massMoment (alignmentEulerMass L) (alignmentEulerMass L*alignmentEulerLogSum L))) :=
    hP.prodMk_nhds (hP.mul hS)
  change Tendsto (fun s : Finset Nat.Primes =>
    ∏ p ∈ s, massMoment (alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
      (alignmentPrimeNumerator (p.val : ℝ) (L.factorization p.val)*Real.log p.val)) atTop _
  convert! hlim using 1
  funext s
  exact alignment_finite_euler_product L s

theorem alignmentEulerMoment_formula {L : ℕ} (hL : 0 < L) :
    alignmentEulerMoment L=alignmentEulerMass L*alignmentEulerLogSum L := by
  have h := (alignment_local_euler_hasProd hL).unique (alignment_normalized_euler_hasProd hL)
  exact congrArg TrivSqZeroExt.snd h

theorem alignment_harmonic_main_euler {L : ℕ} (hL : 0 < L) :
    (∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicLocalMain k)=
      alignmentEulerMass L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L) := by
  calc
    _ = ∑' k : ℕ, (Real.eulerMascheroniConstant*alignmentHarmonicMass L k+
        alignmentHarmonicMoment L k) := by
      apply tsum_congr
      intro k
      unfold harmonicLocalMain alignmentHarmonicMoment alignmentHarmonicMass
        totientSquareWeight logarithmicMark
      ring
    _ = Real.eulerMascheroniConstant*alignmentEulerMass L+alignmentEulerMoment L := by
      rw [((alignmentHarmonicMass_summable hL).mul_left Real.eulerMascheroniConstant).tsum_add
        (alignmentHarmonicMoment_summable hL),tsum_mul_left]
      rfl
    _ = _ := by
      rw [alignmentEulerMoment_formula hL]
      ring

theorem alignment_euler_product {L : ℕ} (hL : 0 < L) :
    3*alignmentConstant L+1=
      (∏' p : Nat.Primes, alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))*
        (Real.eulerMascheroniConstant+
          ∑' p : Nat.Primes, alignmentPrimeAverage (p.val : ℝ) (L.factorization p.val)*Real.log p.val)-
        Real.eulerMascheroniConstant+
        (∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k) ∧
      |∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  have h := alignment_harmonic_approximation hL
  rw [alignment_harmonic_main_euler hL,← alignmentEulerProduct_eq_mass hL] at h
  exact h

theorem alignment_euler_uniform_error {L : ℕ} (hL : 0 < L) :
    |3*alignmentConstant L+1-
      (alignmentEulerProduct L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L)-
        Real.eulerMascheroniConstant)| ≤ zetaNat 2*zetaNat 3/12 := by
  have h := alignment_euler_product hL
  rw [h.1]
  change |alignmentEulerProduct L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L)-
      Real.eulerMascheroniConstant+(∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k)-
      (alignmentEulerProduct L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L)-
        Real.eulerMascheroniConstant)| ≤ _
  simpa only [add_sub_cancel_left] using h.2

end NField.Alignment.CollisionAlignmentEulerProduct
