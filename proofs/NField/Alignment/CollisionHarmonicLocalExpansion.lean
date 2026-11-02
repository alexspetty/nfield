/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeMobiusSeries
import NField.Alignment.CollisionConductorArithmetic
import NField.Alignment.CollisionHarmonicRemainder
import NField.Alignment.CollisionZetaMoments

/-!
# Uniform harmonic expansion of the actual reset coefficients

The coefficient is k times the collision weight. Its finite Mobius
formula is expanded with the proved harmonic remainder. The linear
correction cancels for every k at least two; an explicit divisor bound
controls the remaining error.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicLocalExpansion

open scoped Classical
open ArithmeticFunction CollisionRemainderDynamics CollisionAmplitudeArithmetic
open CollisionAmplitudeMobiusSeries CollisionHarmonicSeed CollisionHarmonicRemainder
open CollisionConductorArithmetic CollisionZetaMoments

def harmonicLocalMain (k : ℕ) : ℝ :=
  (k.totient : ℝ)/(k : ℝ)^2*(Real.log k+Real.eulerMascheroniConstant+nu k)

def harmonicLocalError (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, (moebius d : ℝ)/((k : ℝ)*d)*harmonicError (k/d)

def harmonicLocalErrorBound (k : ℕ) : ℝ :=
  (∑ d ∈ k.divisors, (d : ℝ))/(12*(k : ℝ)^3)

theorem reset_coefficient_moebius {k : ℕ} (hk : 0 < k) :
    (k : ℝ)*collisionWeight k=
      ∑ d ∈ k.divisors, (moebius d : ℝ)/((k : ℝ)*d)*(harmonic (k/d-1) : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [collisionWeight_moebius_convolution,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  unfold moebiusCube cubeKernel harmonicKernel
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

theorem harmonic_local_expansion_term {k d : ℕ} (hk : 0 < k) (hd : d ∈ k.divisors) :
    (moebius d : ℝ)/((k : ℝ)*d)*(harmonic (k/d-1) : ℝ)=
      (1/(k : ℝ))*
        ((Real.log k+Real.eulerMascheroniConstant)*((moebius d : ℝ)/(d : ℝ))-
          (moebius d : ℝ)*Real.log d/(d : ℝ))-
      (1/(2*(k : ℝ)^2))*(moebius d : ℝ)+
      (moebius d : ℝ)/((k : ℝ)*d)*harmonicError (k/d) := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdiv := Nat.div_pos (Nat.le_of_dvd hk hdvd) hdpos
  rw [(strict_harmonic_remainder hdiv).1,Nat.cast_div hdvd hdR,Real.log_div hkR hdR]
  field_simp
  ring

theorem harmonic_local_formula {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ)*collisionWeight k=harmonicLocalMain k+harmonicLocalError k := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  rw [reset_coefficient_moebius (by omega)]
  calc
    _ = ∑ d ∈ k.divisors,
        ((1/(k : ℝ))*
          ((Real.log k+Real.eulerMascheroniConstant)*((moebius d : ℝ)/(d : ℝ))-
            (moebius d : ℝ)*Real.log d/(d : ℝ))-
        (1/(2*(k : ℝ)^2))*(moebius d : ℝ)+
        (moebius d : ℝ)/((k : ℝ)*d)*harmonicError (k/d)) :=
      Finset.sum_congr rfl (fun _ hd => harmonic_local_expansion_term (by omega) hd)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
        ← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,
        moebius_divisor_inverse hk0,moebius_log_divisor hk0,
        CollisionMassInverse.moebius_divisor_sum,if_neg hk1]
      unfold harmonicLocalMain harmonicLocalError totientRatio
      field_simp
      ring

theorem harmonicError_abs_bound {n : ℕ} (hn : 0 < n) :
    |harmonicError n| ≤ 1/(12*(n : ℝ)^2) := by
  have he := harmonicError_bounds hn
  rw [abs_of_neg he.2]
  linarith

theorem harmonic_local_error_term_bound {k d : ℕ} (hk : 0 < k) (hd : d ∈ k.divisors) :
    |(moebius d : ℝ)/((k : ℝ)*d)*harmonicError (k/d)| ≤
      (d : ℝ)/(12*(k : ℝ)^3) := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdiv := Nat.div_pos (Nat.le_of_dvd hk hdvd) hdpos
  have hmu : |(moebius d : ℝ)| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using CollisionMassInverse.moebius_real_norm_le d
  rw [abs_mul,abs_div,abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)*d)]
  calc
    _ ≤ (1/((k : ℝ)*d))*(1/(12*((k/d : ℕ) : ℝ)^2)) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity))
        (harmonicError_abs_bound hdiv) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [Nat.cast_div hdvd hdR]
      field_simp

theorem harmonic_local_error_bound (k : ℕ) :
    |harmonicLocalError k| ≤ harmonicLocalErrorBound k := by
  by_cases hk : k=0
  · simp [hk,harmonicLocalError,harmonicLocalErrorBound]
  unfold harmonicLocalError harmonicLocalErrorBound
  calc
    _ ≤ ∑ d ∈ k.divisors, |(moebius d : ℝ)/((k : ℝ)*d)*harmonicError (k/d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ k.divisors, (d : ℝ)/(12*(k : ℝ)^3) :=
      Finset.sum_le_sum (fun _ hd => harmonic_local_error_term_bound (Nat.pos_of_ne_zero hk) hd)
    _ = _ := by rw [Finset.sum_div]

theorem harmonic_local_expansion {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ)*collisionWeight k=
      (k.totient : ℝ)/(k : ℝ)^2*(Real.log k+Real.eulerMascheroniConstant+
        ∑ p ∈ k.primeFactors, Real.log p/((p : ℝ)-1))+harmonicLocalError k ∧
      |harmonicLocalError k| ≤ (∑ d ∈ k.divisors, (d : ℝ))/(12*(k : ℝ)^3) :=
  ⟨harmonic_local_formula hk,harmonic_local_error_bound k⟩

theorem harmonic_local_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ => (k : ℝ)*collisionWeight k-harmonicLocalMain k)
      (fun k => (∑ d ∈ k.divisors, (d : ℝ))/(k : ℝ)^3) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1/12,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
  rw [harmonic_local_formula hk,add_sub_cancel_left,Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity)]
  convert harmonic_local_error_bound k using 1
  unfold harmonicLocalErrorBound
  ring

end NField.Alignment.CollisionHarmonicLocalExpansion
