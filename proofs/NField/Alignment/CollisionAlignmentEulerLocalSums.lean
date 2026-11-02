/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentEulerJet

/-!
# The local sums in the infinite alignment Euler product

Every prime-power series is evaluated with a HasSum proof. The local mass
is K_p(v); the first moment is the actual alignment numerator times log(p).
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentEulerLocalSums

open scoped Classical
open TrivSqZeroExt CollisionFiniteEulerMoments CollisionAlignmentEulerJet
open CollisionAlignmentPrimeMass CollisionAlignmentLocalSeries CollisionConductorArithmetic

theorem massMoment_hasSum {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun i => massMoment (f i) (g i)) (massMoment a b) := by
  have h := (TrivSqZeroExt.hasSum_inl (M := ℝ) hf).add
    (TrivSqZeroExt.hasSum_inr (R := ℝ) (M := ℝ) hg)
  convert! h using 1
  · funext i
    apply TrivSqZeroExt.ext <;> simp [massMoment]
  · apply TrivSqZeroExt.ext <;> simp [massMoment]

theorem alignmentHarmonicMass_local_hasSum {L p : ℕ} (hL : 0 < L) (hp : p.Prime) :
    HasSum (fun j : ℕ => alignmentHarmonicMass L (p^j))
      (alignmentPrimeFactor (p : ℝ) (L.factorization p)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp_rw [alignmentHarmonicMass_prime_power hL hp]
  exact alignmentPrimeMass_hasSum hp1 _

theorem alignmentHarmonicMoment_local_hasSum {L p : ℕ} (hL : 0 < L) (hp : p.Prime) :
    HasSum (fun j : ℕ => alignmentHarmonicMoment L (p^j))
      (alignmentPrimeNumerator (p : ℝ) (L.factorization p)*Real.log p) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hn : HasSum (alignmentPrimeTerm (p : ℝ) (L.factorization p))
      (alignmentPrimeNumerator (p : ℝ) (L.factorization p)) :=
    (alignmentPrimeNumerator_hasSum hp1 _).summable.hasSum
  have hs : HasSum (fun j : ℕ => alignmentHarmonicMoment L (p^(j+1)))
      (alignmentPrimeNumerator (p : ℝ) (L.factorization p)*Real.log p) := by
    exact (hn.mul_right (Real.log p)).congr_fun
      (fun j => alignmentHarmonicMoment_prime_power hL hp j)
  have hz : alignmentHarmonicMoment L (p^0)=0 := by
    simp [alignmentHarmonicMoment,logarithmicMark,nu]
  have h := hs.zero_add (f := fun j : ℕ => alignmentHarmonicMoment L (p^j))
  simpa only [hz,zero_add] using h

theorem alignmentJet_local_hasSum {L p : ℕ} (hL : 0 < L) (hp : p.Prime) :
    HasSum (fun j : ℕ => alignmentJet L (p^j))
      (massMoment (alignmentPrimeFactor (p : ℝ) (L.factorization p))
        (alignmentPrimeNumerator (p : ℝ) (L.factorization p)*Real.log p)) := by
  change HasSum (fun j : ℕ => massMoment (alignmentHarmonicMass L (p^j))
    (alignmentHarmonicMoment L (p^j))) _
  exact massMoment_hasSum (alignmentHarmonicMass_local_hasSum hL hp)
    (alignmentHarmonicMoment_local_hasSum hL hp)

def alignmentEulerMass (L : ℕ) : ℝ := ∑' k : ℕ, alignmentHarmonicMass L k

def alignmentEulerMoment (L : ℕ) : ℝ := ∑' k : ℕ, alignmentHarmonicMoment L k

theorem alignmentJet_global_hasSum {L : ℕ} (hL : 0 < L) :
    HasSum (alignmentJet L) (massMoment (alignmentEulerMass L) (alignmentEulerMoment L)) :=
  massMoment_hasSum (alignmentHarmonicMass_summable hL).hasSum
    (alignmentHarmonicMoment_summable hL).hasSum

theorem alignment_local_euler_hasProd {L : ℕ} (hL : 0 < L) :
    HasProd (fun p : Nat.Primes =>
      massMoment (alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val))
        (alignmentPrimeNumerator (p.val : ℝ) (L.factorization p.val)*Real.log p.val))
      (massMoment (alignmentEulerMass L) (alignmentEulerMoment L)) := by
  have h := alignmentJet_euler_hasProd hL
  rw [(alignmentJet_global_hasSum hL).tsum_eq] at h
  convert! h using 1
  funext p
  exact (alignmentJet_local_hasSum hL p.property).tsum_eq.symm

theorem alignmentEulerMass_lower {L : ℕ} (hL : 0 < L) : 1 ≤ alignmentEulerMass L := by
  have h := (alignmentHarmonicMass_summable hL).le_tsum 1
    (fun k _ => alignmentHarmonicMass_nonneg L k)
  have h1 : alignmentHarmonicMass L 1=1 := by simp [alignmentHarmonicMass,totientSquareWeight]
  change 1 ≤ ∑' k : ℕ, alignmentHarmonicMass L k
  simpa only [h1] using h

end NField.Alignment.CollisionAlignmentEulerLocalSums
