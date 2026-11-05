/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicRootAverage
import NField.Alignment.CollisionAmplitudeRefinement
import NField.Alignment.CollisionCotangentMixedMoment
import NField.Alignment.ReducedHarmonicMobius

/-!
# The cotangent and mixed-moment formulas for the original amplitude

The actual harmonic-seed root average is inserted into the already proved
amplitude transform. Its three terms are transformed separately, including
the zero ordinary Mobius sum when q>1.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeCotangent

open scoped BigOperators
open CollisionHarmonicRootAverage CollisionHarmonicSeed CollisionAmplitudeArithmetic
open CollisionAmplitudeRefinement CollisionCotangentSeries CollisionCotangentMixedMoment
open CollisionJordanVariance

theorem reciprocalCube_moebius_divisor_sum {q : ℕ} (hq : 0<q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)=deltaThree q := by
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun n => jordanThree n) (g := fun n => (n : ℝ)^3)).mp
      (fun n _ => sum_jordanThree_divisors n) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a : ℝ)*(b : ℝ)^3)] at hb
  have hqR : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr hq.ne'
  apply mul_left_cancel₀ (pow_ne_zero 3 hqR)
  rw [← jordanThree_euler_product hq.ne',← hb,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

theorem harmonic_seed_moebius_cotangent {q : ℕ} (hq : 1<q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d))=
      zetaThree/2*deltaThree q-Real.pi/(2*(q : ℝ))*unitCotangentSum q := by
  have hqpos : 0<q := by omega
  have hqR : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr hqpos.ne'
  have heq (d : ℕ) (hd : d∈q.divisors) :
      (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d)=
        zetaThree/2*((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)+
        zetaThree/(2*(q : ℝ)^3)*(ArithmeticFunction.moebius d : ℝ)-
        Real.pi/(2*(q : ℝ))*((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2*cotangentSum (q/d)) := by
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdR : (d : ℝ)≠0 := Nat.cast_ne_zero.mpr hdpos.ne'
    have hdiv : 0<q/d := Nat.div_pos (Nat.le_of_dvd hqpos (Nat.dvd_of_mem_divisors hd)) hdpos
    rw [literal_harmonic_root_average hdiv,Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
    field_simp
  rw [Finset.sum_congr rfl heq,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,
    reciprocalCube_moebius_divisor_sum hqpos,unitCotangentSum_moebius hqpos]
  have hmu : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ))=0 := by
    simpa only [if_neg (by omega : q≠1)] using ReducedHarmonicMobius.sum_moebius_divisors q
  rw [hmu,mul_zero,add_zero]

theorem literal_amplitude_cotangent {q : ℕ} (hq : 1<q) :
    amplitude q=1/2-Real.pi/(2*(q : ℝ)*zetaThree*deltaThree q)*unitCotangentSum q := by
  rw [amplitude_exact_transform (by omega : 0<q),harmonic_seed_moebius_cotangent hq]
  have hz : zetaThree≠0 := zetaThree_pos.ne'
  have hd : deltaThree q≠0 := (deltaThree_pos q).ne'
  field_simp

theorem literal_original_amplitude_mixed_moment {q : ℕ} [NeZero q] (hq : 2≤q) :
    (amplitude q : ℂ)=1/2-cotangentCharacterMoment q/
      ((zetaThree : ℂ)*(deltaThree q : ℂ)*(Nat.totient q : ℂ)) := by
  have hqpos : 0<q := by omega
  have hqC : (q : ℂ)≠0 := Nat.cast_ne_zero.mpr hqpos.ne'
  have hpi : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := congrArg Complex.ofReal (literal_amplitude_cotangent (by omega : 1<q))
  push_cast at h
  rw [literal_unit_cotangent_mixed_moment hq] at h
  rw [h,mixedMomentScale]
  field_simp

theorem original_amplitude_two : amplitude 2=1/2 := by
  rw [literal_amplitude_cotangent (by norm_num),unitCotangentSum_two]
  ring

end NField.Alignment.CollisionAmplitudeCotangent
