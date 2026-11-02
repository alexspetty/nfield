/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeRefinement
import NField.Alignment.CollisionMassInverse

/-!
# The absolutely convergent infinite Mobius extraction

This independently covers the supporting infinite series in the written
amplitude proof. The domination is by the positive product of two proved
summable series, before any fiber or row rearrangement.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeMobiusSeries

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionMassReadout CollisionReciprocalBudget
open CollisionAmplitudeArithmetic CollisionHarmonicSeed CollisionJordanVariance

def moebiusCube (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ)*cubeKernel d

@[simp] theorem moebiusCube_zero : moebiusCube 0=0 := by simp [moebiusCube]

theorem moebiusCube_norm (d : ℕ) : ‖moebiusCube d‖≤cubeKernel d := by
  rw [moebiusCube, norm_mul, Real.norm_of_nonneg (cubeKernel_nonneg d)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (CollisionMassInverse.moebius_real_norm_le d) (cubeKernel_nonneg d)

theorem moebiusCube_summable : Summable moebiusCube :=
  Summable.of_norm_bounded cubeKernel_summable moebiusCube_norm

theorem collisionWeight_moebius_convolution (n : ℕ) :
    collisionWeight n=∑ d ∈ n.divisors, moebiusCube d*harmonicKernel (n/d) := by
  by_cases hn : n=0
  · simp [hn]
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun k => (k : ℝ)^3*collisionWeight k)
    (g := fun n => (n : ℝ)*(harmonic (n-1) : ℝ))).mp
      (fun _ hn => reciprocal_budget hn) n (Nat.pos_of_ne_zero hn)
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℝ)*
    ((y : ℝ)*(harmonic (y-1) : ℝ)))] at hb
  apply mul_left_cancel₀ (pow_ne_zero 3 hnR)
  rw [← hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  unfold moebiusCube cubeKernel harmonicKernel
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

def moebiusDouble (q : ℕ) (p : ℕ×ℕ) : ℝ :=
  if q∣p.1*p.2 then moebiusCube p.1*harmonicKernel p.2 else 0

theorem moebiusDouble_summable (q : ℕ) : Summable (moebiusDouble q) := by
  have hs := cubeKernel_summable.mul_of_nonneg harmonicKernel_hasSum.summable
    cubeKernel_nonneg harmonicKernel_nonneg
  apply Summable.of_norm_bounded hs
  intro p
  unfold moebiusDouble
  split_ifs
  · rw [norm_mul, Real.norm_of_nonneg (harmonicKernel_nonneg p.2)]
    exact mul_le_mul_of_nonneg_right (moebiusCube_norm p.1) (harmonicKernel_nonneg p.2)
  · simp only [norm_zero]
    exact mul_nonneg (cubeKernel_nonneg p.1) (harmonicKernel_nonneg p.2)

theorem moebiusDouble_fiber (q n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, moebiusDouble q p.val)=
      if q∣n then collisionWeight n else 0 := by
  have he : (fun p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n} => moebiusDouble q p.val)=
      fun p => if q∣n then moebiusCube p.val.1*harmonicKernel p.val.2 else 0 := by
    funext p
    unfold moebiusDouble
    rw [show p.val.1*p.val.2=n from p.property]
  rw [he]
  split_ifs
  · rw [divisor_product_fiber moebiusCube harmonicKernel moebiusCube_zero
      (by simp [harmonicKernel]), ← collisionWeight_moebius_convolution]
  · exact tsum_zero

theorem amplitude_eq_moebiusDouble (q : ℕ) :
    amplitude q=∑' p, moebiusDouble q p := by
  have hf := (moebiusDouble_summable q).hasSum.tsum_fiberwise
    (fun p : ℕ×ℕ => p.1*p.2)
  simp_rw [moebiusDouble_fiber] at hf
  exact hf.tsum_eq

theorem moebiusDouble_row {q : ℕ} (hq : 0<q) (d : ℕ) :
    (∑' m, moebiusDouble q (d,m))=moebiusCube d*harmonicSeed (q/(q.gcd d)) := by
  have he (m : ℕ) : moebiusDouble q (d,m)=moebiusCube d*
      (if q/(q.gcd d)∣m then harmonicKernel m else 0) := by
    unfold moebiusDouble
    simp only [divides_product_iff_reduced hq]
    split_ifs <;> simp
  simp_rw [he]
  rw [tsum_mul_left, ← tsum_multiples
    (Nat.div_pos (Nat.gcd_le_left d hq) (Nat.gcd_pos_of_pos_left d hq))]
  rfl

theorem amplitude_infinite_moebius {q : ℕ} (hq : 0<q) :
    amplitude q=∑' d, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*
      harmonicSeed (q/(q.gcd d)) := by
  rw [amplitude_eq_moebiusDouble, (moebiusDouble_summable q).tsum_prod]
  simp_rw [moebiusDouble_row hq]
  simp only [moebiusCube, cubeKernel, mul_one_div]

theorem amplitude_infinite_moebius_summable {q : ℕ} (hq : 0<q) :
    Summable (fun d => (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*
      harmonicSeed (q/(q.gcd d))) := by
  have hs := (moebiusDouble_summable q).prod
  simpa only [moebiusDouble_row hq, moebiusCube, cubeKernel, mul_one_div] using hs

theorem amplitude_positive_moebius_series {q : ℕ} (hq : 0<q) :
    HasSum (fun d => (ArithmeticFunction.moebius (d+1) : ℝ)/((d+1 : ℕ) : ℝ)^3*
      harmonicSeed (q/(q.gcd (d+1)))) (amplitude q) := by
  have hs := amplitude_infinite_moebius_summable hq
  have he := hs.sum_add_tsum_nat_add 1
  have ht : (∑' d, (ArithmeticFunction.moebius (d+1) : ℝ)/((d+1 : ℕ) : ℝ)^3*
      harmonicSeed (q/(q.gcd (d+1))))=amplitude q := by
    simpa [← amplitude_infinite_moebius hq] using he
  rw [← ht]
  exact (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).hasSum

end NField.Alignment.CollisionAmplitudeMobiusSeries
