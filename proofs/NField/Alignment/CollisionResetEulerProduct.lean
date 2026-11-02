/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteEulerMoments
import NField.Alignment.CollisionHarmonicObservableApproximation
import NField.Alignment.CollisionAlignmentPrimeMass

/-!
# The reset Euler product with a uniform error

The actual finite divisor reset is expressed through every prime-power
factor of the observation. Both its mass and logarithmic first moment
are carried through the finite product. The independently summable
harmonic error gives one constant for every positive observation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResetEulerProduct

open scoped Classical
open TrivSqZeroExt CollisionFiniteEulerMoments CollisionResetLocalFactors
open CollisionAlignmentPrimeMass CollisionHarmonicLocalExpansion CollisionZetaMoments
open CollisionHarmonicObservableApproximation CollisionConductorArithmetic

def resetEulerProduct (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, resetPrimeFactor (p : ℝ) (n.factorization p)

def resetEulerLogSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, resetPrimeAverage (p : ℝ) (n.factorization p)*Real.log p

theorem harmonicJet_prime_power_sum {p : ℕ} (hp : p.Prime) (v : ℕ) :
    (∑ j ∈ Finset.range (v+1), harmonicJet (p^j))=
      ((resetPrimeFactor (p : ℝ) v,resetPrimeNumerator (p : ℝ) v*Real.log p) : DualNumber ℝ) := by
  apply TrivSqZeroExt.ext
  · rw [fst_sum]
    change (∑ j ∈ Finset.range (v+1), totientSquareWeight (p^j))=resetPrimeFactor (p : ℝ) v
    rw [Finset.sum_range_succ']
    simp_rw [totientSquareWeight_prime_power hp]
    simpa [totientSquareWeight,add_comm] using (resetPrimeFactor_mass_sum (p : ℝ) v).symm
  · rw [snd_sum]
    change (∑ j ∈ Finset.range (v+1), totientSquareWeight (p^j)*logarithmicMark (p^j))=
      resetPrimeNumerator (p : ℝ) v*Real.log p
    rw [Finset.sum_range_succ']
    simp_rw [totientSquareWeight_prime_power hp,logarithmicMark_prime_power hp]
    have hz : totientSquareWeight (p^0)*logarithmicMark (p^0)=0 := by
      simp [totientSquareWeight,logarithmicMark,nu]
    rw [hz,add_zero,resetPrimeNumerator,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem reset_harmonic_euler_jet {n : ℕ} (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, harmonicJet k)=
      ((resetEulerProduct n,resetEulerProduct n*resetEulerLogSum n) : DualNumber ℝ) := by
  rw [multiplicative_divisor_euler harmonicJet harmonicJet_multiplicative hn]
  have ha (p : ℕ) (hp : p ∈ n.primeFactors) : resetPrimeFactor (p : ℝ) (n.factorization p) ≠ 0 := by
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le
      (resetPrimeFactor_bounds hp1 _).1)
  calc
    _ = ∏ p ∈ n.primeFactors,
        massMoment (resetPrimeFactor (p : ℝ) (n.factorization p))
          (resetPrimeNumerator (p : ℝ) (n.factorization p)*Real.log p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact harmonicJet_prime_power_sum (Nat.prime_of_mem_primeFactors hp) _
    _ = ((resetEulerProduct n,resetEulerProduct n*
        (∑ p ∈ n.primeFactors, (resetPrimeNumerator (p : ℝ) (n.factorization p)*Real.log p)/
          resetPrimeFactor (p : ℝ) (n.factorization p))) : DualNumber ℝ) :=
      dual_product_mass_moment n.primeFactors _ _ ha
    _ = _ := by
      apply TrivSqZeroExt.ext
      · rfl
      · change resetEulerProduct n*(∑ p ∈ n.primeFactors, _)=resetEulerProduct n*resetEulerLogSum n
        congr 1
        unfold resetEulerLogSum
        apply Finset.sum_congr rfl
        intro p hp
        unfold resetPrimeAverage
        ring

theorem harmonicLocalMain_jet (k : ℕ) :
    harmonicLocalMain k=Real.eulerMascheroniConstant*(harmonicJet k).fst+(harmonicJet k).snd := by
  change harmonicLocalMain k=Real.eulerMascheroniConstant*totientSquareWeight k+
    totientSquareWeight k*logarithmicMark k
  unfold harmonicLocalMain totientSquareWeight logarithmicMark
  ring

theorem reset_harmonic_main_euler {n : ℕ} (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, harmonicLocalMain k)=
      resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n) := by
  calc
    _ = Real.eulerMascheroniConstant*(∑ k ∈ n.divisors, harmonicJet k).fst+
        (∑ k ∈ n.divisors, harmonicJet k).snd := by
      rw [fst_sum,snd_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => harmonicLocalMain_jet k)
    _ = _ := by
      rw [reset_harmonic_euler_jet hn]
      simp only [fst_mk,snd_mk]
      ring

theorem reset_euler_product {n : ℕ} (hn : 0 < n) :
    (∑' k, CollisionResolutionLaw.resetTerm n k)=
      (∏ p ∈ n.primeFactors, resetPrimeFactor (p : ℝ) (n.factorization p))*
        (Real.eulerMascheroniConstant+
          ∑ p ∈ n.primeFactors, resetPrimeAverage (p : ℝ) (n.factorization p)*Real.log p)-
        Real.eulerMascheroniConstant+(∑ k ∈ n.divisors, harmonicGlobalError k) ∧
      |∑ k ∈ n.divisors, harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  have h := reset_harmonic_approximation hn
  rw [reset_harmonic_main_euler hn.ne'] at h
  exact h

theorem reset_euler_uniform_error {n : ℕ} (hn : 0 < n) :
    |(∑' k, CollisionResolutionLaw.resetTerm n k)-
      (resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n)-
        Real.eulerMascheroniConstant)| ≤ zetaNat 2*zetaNat 3/12 := by
  have h := reset_euler_product hn
  rw [h.1]
  change |resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n)-
      Real.eulerMascheroniConstant+(∑ k ∈ n.divisors, harmonicGlobalError k)-
      (resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n)-
        Real.eulerMascheroniConstant)| ≤ _
  simpa only [add_sub_cancel_left] using h.2

end NField.Alignment.CollisionResetEulerProduct
