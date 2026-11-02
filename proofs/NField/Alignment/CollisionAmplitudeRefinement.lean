/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicSeed

/-!
# Exact amplitude refinement

The positive reciprocal-address budget gives the full harmonic seed.
Finite Jordan expansion and Mobius inversion then yield the manuscript's
exact transform for the already defined amplitudes, including conductor one.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAmplitudeRefinement

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance
open CollisionAmplitudeArithmetic CollisionHarmonicSeed

theorem cubeKernel_div_gcd {q : ℕ} (hq : 0<q) (d : ℕ) :
    cubeKernel (q/(q.gcd d))=((q.gcd d : ℕ) : ℝ)^3/(q : ℝ)^3 := by
  have hgR : ((q.gcd d : ℕ) : ℝ)≠0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left d hq).ne'
  rw [cubeKernel, Nat.cast_div (Nat.gcd_dvd_left q d) hgR]
  field_simp

theorem harmonicSeed_gcd {q : ℕ} (hq : 0<q) :
    harmonicSeed q=zetaThree/(q : ℝ)^3*
      ∑' d, collisionWeight d*((q.gcd d : ℕ) : ℝ)^3 := by
  rw [harmonicSeed_gcd_reduced hq]
  simp_rw [cubeKernel_div_gcd hq, ← mul_div_assoc]
  rw [tsum_div_const]
  ring

theorem gcd_jordanThree {q : ℕ} (hq : 0<q) (d : ℕ) :
    ((q.gcd d : ℕ) : ℝ)^3=∑ e ∈ q.divisors, if e∣d then jordanThree e else 0 := by
  have hset : (q.gcd d).divisors=q.divisors.filter (fun e => e∣d) := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · intro h; exact ⟨⟨h.1.1,hq.ne'⟩,h.1.2⟩
    · intro h; exact ⟨⟨h.1.1,h.2⟩,(Nat.gcd_pos_of_pos_left d hq).ne'⟩
  rw [← sum_jordanThree_divisors, hset, Finset.sum_filter]

theorem weightedGcd_summable {q : ℕ} (hq : 0<q) :
    Summable (fun d => collisionWeight d*((q.gcd d : ℕ) : ℝ)^3) := by
  apply Summable.of_nonneg_of_le (fun d => mul_nonneg (collisionWeight_nonneg d) (by positivity)) _
    (collisionWeight_summable.mul_right ((q : ℝ)^3))
  intro d
  apply mul_le_mul_of_nonneg_left _ (collisionWeight_nonneg d)
  apply pow_le_pow_left₀ (by positivity) _ 3
  exact_mod_cast Nat.gcd_le_left d hq

theorem weightedGcd_eq_jordan_budget {q : ℕ} (hq : 0<q) :
    (∑' d, collisionWeight d*((q.gcd d : ℕ) : ℝ)^3)=
      ∑ e ∈ q.divisors, jordanThree e*amplitude e := by
  calc
    _ = ∑' d, ∑ e ∈ q.divisors, jordanThree e*(if e∣d then collisionWeight d else 0) := by
      apply tsum_congr
      intro d
      rw [gcd_jordanThree hq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ = ∑ e ∈ q.divisors, ∑' d, jordanThree e*(if e∣d then collisionWeight d else 0) :=
      Summable.tsum_finsetSum (fun e _ => (amplitude_summable e).mul_left (jordanThree e))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      exact tsum_mul_left

theorem amplitude_jordan_budget {q : ℕ} (hq : 0<q) :
    (∑ d ∈ q.divisors, jordanThree d*amplitude d)=(q : ℝ)^3*harmonicSeed q/zetaThree := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  rw [harmonicSeed_gcd hq, weightedGcd_eq_jordan_budget hq]
  field_simp [zetaThree_pos.ne']

theorem amplitude_one : amplitude 1=1 := by
  simpa [amplitude] using collisionWeight_hasSum.tsum_eq

theorem amplitude_moebius_budget {q : ℕ} (hq : 0<q) :
    jordanThree q*amplitude q=
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)*
        (((q/d : ℕ) : ℝ)^3*harmonicSeed (q/d)/zetaThree) := by
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun d => jordanThree d*amplitude d)
    (g := fun n => (n : ℝ)^3*harmonicSeed n/zetaThree)).mp
      (fun n hn => amplitude_jordan_budget hn) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℝ)*
    ((y : ℝ)^3*harmonicSeed y/zetaThree))] at hb
  exact hb.symm

theorem amplitude_exact_transform {q : ℕ} (hq : 0<q) :
    amplitude q=1/(zetaThree*deltaThree q)*
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d) := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hz := zetaThree_pos.ne'
  have hd := (deltaThree_pos q).ne'
  have hb := amplitude_moebius_budget hq
  have hs : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)*
        (((q/d : ℕ) : ℝ)^3*harmonicSeed (q/d)/zetaThree)) =
      (q : ℝ)^3/zetaThree*
        ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdvd
    have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hdvd).ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hdvd) hdR]
    field_simp
  rw [hs, jordanThree_euler_product hq.ne'] at hb
  apply (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hqR) hd))
  rw [hb]
  field_simp

theorem exact_amplitude_refinement {q : ℕ} (hq : 1≤q) :
    Summable (fun m => (harmonic (q*(m+1)-1) : ℝ)/((q*(m+1) : ℕ) : ℝ)^2) ∧
    amplitude q=1/(zetaThree*deltaThree q)*
      (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d)) ∧
    (∑ d ∈ q.divisors, jordanThree d*amplitude d)=(q : ℝ)^3*harmonicSeed q/zetaThree ∧
    harmonicSeed 1=zetaThree ∧ (zetaThree : ℂ)=riemannZeta 3 ∧ amplitude 1=1 := by
  refine ⟨?_, amplitude_exact_transform hq, amplitude_jordan_budget hq,
    harmonicSeed_one, zetaThree_eq_riemannZeta, amplitude_one⟩
  exact (harmonicSeed_summable hq).comp_injective (fun _ _ h => Nat.add_right_cancel h)

end NField.Alignment.CollisionAmplitudeRefinement
