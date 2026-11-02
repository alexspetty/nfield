/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResetEulerProduct
import Mathlib.Analysis.Normed.Algebra.DualNumber
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# An absolutely summable arithmetic jet for alignment

The mass retains gcd(k,L), and the second component retains its actual
logarithmic first moment. Summability precedes the infinite Euler product.
Every prime is included, whether or not it divides the positive modulus.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentEulerJet

open scoped Classical
open ArithmeticFunction TrivSqZeroExt CollisionFiniteEulerMoments
open CollisionHarmonicLocalExpansion CollisionHarmonicObservableApproximation
open CollisionAlignmentPrimeMass CollisionAlignmentLocalSeries CollisionConductorArithmetic
open CollisionZetaMoments

def alignmentHarmonicMass (L k : ℕ) : ℝ :=
  (k.gcd L : ℝ)/(k : ℝ)*totientSquareWeight k

def alignmentHarmonicMoment (L k : ℕ) : ℝ := alignmentHarmonicMass L k*logarithmicMark k

def alignmentJet (L : ℕ) : ArithmeticFunction (DualNumber ℝ) where
  toFun k := massMoment (alignmentHarmonicMass L k) (alignmentHarmonicMoment L k)
  map_zero' := by
    apply TrivSqZeroExt.ext <;>
      simp [massMoment,alignmentHarmonicMass,alignmentHarmonicMoment]

theorem alignmentHarmonicMass_mul (L : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    alignmentHarmonicMass L (m*n)=alignmentHarmonicMass L m*alignmentHarmonicMass L n := by
  have hg : (m*n).gcd L=m.gcd L*n.gcd L := by
    simpa only [Nat.gcd_comm] using hmn.gcd_mul L
  simp only [alignmentHarmonicMass,hg,Nat.cast_mul,totientSquareWeight_mul hmn]
  ring

theorem alignmentJet_multiplicative (L : ℕ) : (alignmentJet L).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  constructor
  · apply TrivSqZeroExt.ext <;>
      simp [alignmentJet,massMoment,alignmentHarmonicMass,alignmentHarmonicMoment,
        totientSquareWeight,logarithmicMark,nu]
  · intro m n hm hn hmn
    apply TrivSqZeroExt.ext
    · change alignmentHarmonicMass L (m*n)=alignmentHarmonicMass L m*alignmentHarmonicMass L n
      exact alignmentHarmonicMass_mul L hmn
    · change alignmentHarmonicMass L (m*n)*logarithmicMark (m*n)=
        alignmentHarmonicMass L m*(alignmentHarmonicMass L n*logarithmicMark n)+
          (alignmentHarmonicMass L m*logarithmicMark m)*alignmentHarmonicMass L n
      rw [alignmentHarmonicMass_mul L hmn,logarithmicMark_mul hm hn hmn]
      ring

theorem alignmentHarmonicMass_nonneg (L k : ℕ) : 0 ≤ alignmentHarmonicMass L k := by
  unfold alignmentHarmonicMass totientSquareWeight
  positivity

theorem alignmentHarmonicMass_bound {L : ℕ} (hL : 0 < L) (k : ℕ) :
    alignmentHarmonicMass L k ≤ (L : ℝ)*powerKernel 2 k := by
  by_cases hk : k=0
  · simp [hk,alignmentHarmonicMass,powerKernel]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hg : (k.gcd L : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.gcd_le_right k hL
  have ht : (k.totient : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.totient_le k
  calc
    _ = (k.gcd L : ℝ)*(k.totient : ℝ)/(k : ℝ)^3 := by
      unfold alignmentHarmonicMass totientSquareWeight
      field_simp
    _ ≤ (L : ℝ)*(k : ℝ)/(k : ℝ)^3 :=
      div_le_div_of_nonneg_right (mul_le_mul hg ht (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (by positivity)
    _ = _ := by
      unfold powerKernel
      field_simp

theorem alignmentHarmonicMass_summable {L : ℕ} (hL : 0 < L) :
    Summable (alignmentHarmonicMass L) :=
  Summable.of_nonneg_of_le (alignmentHarmonicMass_nonneg L) (alignmentHarmonicMass_bound hL)
    ((powerKernel_summable (by norm_num : 1 < (2 : ℕ))).mul_left (L : ℝ))

theorem alignmentHarmonicMoment_summable {L : ℕ} (hL : 0 < L) :
    Summable (alignmentHarmonicMoment L) := by
  have h := (alignment_harmonic_main_summable hL).sub
    ((alignmentHarmonicMass_summable hL).mul_left Real.eulerMascheroniConstant)
  apply h.congr
  intro k
  unfold alignmentHarmonicMoment alignmentHarmonicMass harmonicLocalMain
    totientSquareWeight logarithmicMark
  ring

theorem alignmentJet_norm_summable {L : ℕ} (hL : 0 < L) :
    Summable (fun k : ℕ => ‖alignmentJet L k‖) := by
  have h := (alignmentHarmonicMass_summable hL).norm.add (alignmentHarmonicMoment_summable hL).norm
  have he (k : ℕ) : ‖alignmentJet L k‖=
      ‖alignmentHarmonicMass L k‖+‖alignmentHarmonicMoment L k‖ := by
    rw [TrivSqZeroExt.norm_def]
    rfl
  exact h.congr (fun k => (he k).symm)

theorem alignmentJet_euler_hasProd {L : ℕ} (hL : 0 < L) :
    HasProd (fun p : Nat.Primes => ∑' j : ℕ, alignmentJet L (p.val^j))
      (∑' k : ℕ, alignmentJet L k) :=
  (alignmentJet_multiplicative L).eulerProduct_hasProd (alignmentJet_norm_summable hL)

theorem prime_power_gcd_factorization {L p : ℕ} (hL : 0 < L) (hp : p.Prime) (j : ℕ) :
    (p^j).gcd L=p^(min j (L.factorization p)) := by
  apply Nat.factorization_inj
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left L (Nat.pow_pos hp.pos))) (pow_ne_zero _ hp.ne_zero)
  rw [Nat.factorization_gcd (pow_ne_zero _ hp.ne_zero) hL.ne',hp.factorization_pow,hp.factorization_pow]
  ext q
  by_cases hq : q=p
  · subst q
    simp
  · simp [hq]

theorem alignmentHarmonicMass_prime_power {L p : ℕ} (hL : 0 < L) (hp : p.Prime) (j : ℕ) :
    alignmentHarmonicMass L (p^j)=alignmentPrimeMass (p : ℝ) (L.factorization p) j := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [alignmentPrimeMass_totient hp]
  unfold alignmentHarmonicMass totientSquareWeight
  rw [prime_power_gcd_factorization hL hp]
  simp only [Nat.cast_pow]
  rw [show 3*j=j*3 by omega,pow_mul]
  field_simp

theorem alignmentHarmonicMoment_prime_power {L p : ℕ} (hL : 0 < L) (hp : p.Prime) (j : ℕ) :
    alignmentHarmonicMoment L (p^(j+1))=
      alignmentPrimeTerm (p : ℝ) (L.factorization p) j*Real.log p := by
  unfold alignmentHarmonicMoment
  rw [alignmentHarmonicMass_prime_power hL hp,logarithmicMark_prime_power hp]
  simp only [alignmentPrimeMass,Nat.add_one_ne_zero,if_false]
  unfold alignmentPrimeTerm
  ring

end NField.Alignment.CollisionAlignmentEulerJet
