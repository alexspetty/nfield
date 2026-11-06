/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.NearOneDivisorEuler
import NField.Alignment.NearOnePrimeWeights
import NField.Alignment.HarperSmoothDivisor
import NField.Alignment.SawtoothGcdWeightedFrequency

/-! # A pointwise near-one reciprocal-divisor bound and its actual Fourier consumer -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.NearOneReciprocalDivisorBound
open CollisionMertensInput NearOneDivisorEuler NearOnePrimeWeights Filter
open scoped BigOperators Classical Topology

/-- Mertens' inverse prime product dominates the exponential reciprocal-prime sum. -/
theorem exponential_reciprocal_sum_le_product (Y : ℝ) :
    Real.exp (∑ p ∈ primesUpTo Y, 1/(p : ℝ)) ≤ inversePrimeProduct Y := by
  rw [Real.exp_sum]
  unfold inversePrimeProduct
  apply Finset.prod_le_prod
  · intro p hp
    exact (Real.exp_pos _).le
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (primesUpTo_mem.mp hp).1.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have ht : 1/(p : ℝ) < 1 := (div_lt_one hp0).mpr hp1
    have hd : 0 < 1-1/(p : ℝ) := by linarith
    have hl := Real.log_le_sub_one_of_pos hd
    have hh : 1/(p : ℝ) ≤ -Real.log (1-1/(p : ℝ)) := by linarith
    have he := Real.exp_le_exp.mpr hh
    rw [Real.exp_neg, Real.exp_log hd] at he
    simpa only [one_div] using he

/-- Splitting actual prime factors at log n gives a pointwise product bound uniformly in epsilon. -/
theorem divisor_sum_le_inverse_product {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hL : 1 < Real.log (n : ℝ)) (hLL : 1 ≤ Real.log (Real.log (n : ℝ)))
    (he0 : 0 ≤ ε) (he : ε ≤ 1/2) (hlog : ε*Real.log (Real.log (n : ℝ)) ≤ 1) :
    (∑ d ∈ n.divisors, (d : ℝ)^(ε-1)) ≤
      Real.exp 12*(inversePrimeProduct (Real.log n))^12 := by
  have hEuler := divisor_power_sum_le_exp hn (ε-1) (by
    intro p hp
    exact prime_weight_le_three_quarters (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) he)
  have hPrime := prime_factor_weight_sum hn hL he0 he hlog
  have hthree : 3/Real.log (Real.log (n : ℝ)) ≤ 3 := div_le_self (by norm_num) hLL
  have hsum : 4*(∑ p ∈ n.primeFactors, (p : ℝ)^(ε-1)) ≤
      12*(∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ))+12 := by linarith
  calc
    _ ≤ Real.exp (4*∑ p ∈ n.primeFactors, (p : ℝ)^(ε-1)) := hEuler
    _ ≤ Real.exp (12*(∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ))+12) := Real.exp_le_exp.mpr hsum
    _ = Real.exp 12*(Real.exp (∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ)))^12 := by
      rw [Real.exp_add, show Real.exp (12*(∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ))) =
        (Real.exp (∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ)))^12 by
          simpa using Real.exp_nat_mul (∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ)) 12]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.exp_pos _).le (exponential_reciprocal_sum_le_product (Real.log n)) 12) (Real.exp_pos _).le

/-- One absolute constant controls every admissible near-one exponent pointwise, not only on average. -/
theorem eventual_pointwise_bound : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/2 → ε*Real.log (Real.log (n : ℝ)) ≤ 1 →
      (∑ d ∈ n.divisors, (d : ℝ)^(ε-1)) ≤ K*(Real.log (Real.log n))^12 := by
  obtain ⟨C, hC, hbound⟩ := HarperSmoothDivisor.uniform_smooth_divisor_estimate
  refine ⟨Real.exp 12*C^12, by positivity, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually hbound, hlog.eventually_gt_atTop 1,
    hloglog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with n hp hL hLL hn ε he0 he hsmall
  have hnpos : 0 < n := by omega
  have hProd : inversePrimeProduct (Real.log n) ≤ C*Real.log (Real.log n) := by
    simpa using (hp 1 (by norm_num)).2
  calc
    _ ≤ Real.exp 12*(inversePrimeProduct (Real.log n))^12 := divisor_sum_le_inverse_product hnpos hL hLL he0 he hsmall
    _ ≤ Real.exp 12*(C*Real.log (Real.log n))^12 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (inversePrimeProduct_pos _).le hProd 12
    _ = _ := by rw [mul_pow]; ring

/-- The actual weighted sawtooth Fourier sum has a uniform pointwise near-one bound. -/
theorem eventual_weighted_frequency_bound : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ [NeZero n], ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/2 → ε*Real.log (Real.log (n : ℝ)) ≤ 1 →
      (∑ j : ZMod n, ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod n → ℂ) j‖ *
        (j.val.gcd n : ℝ)^ε)/(n : ℝ) ≤
          K*(harmonic n : ℝ)*(Real.log (Real.log n))^12 := by
  obtain ⟨C, hC, hbound⟩ := eventual_pointwise_bound
  refine ⟨C/2, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with n hn hn2 inst ε he0 he hsmall
  have hH : (0 : ℝ) ≤ harmonic n := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic n by unfold harmonic; positivity)
  calc
    _ ≤ (harmonic n : ℝ)/2*∑ d ∈ n.divisors, (d : ℝ)^(ε-1) :=
      SawtoothGcdWeightedFrequency.rpow_frequency_bound hn2 ε
    _ ≤ (harmonic n : ℝ)/2*(C*(Real.log (Real.log n))^12) :=
      mul_le_mul_of_nonneg_left (hn ε he0 he hsmall) (by positivity)
    _ = _ := by ring

end NField.Alignment.NearOneReciprocalDivisorBound
