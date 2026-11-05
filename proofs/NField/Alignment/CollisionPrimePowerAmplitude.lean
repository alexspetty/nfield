/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionUniformAmplitude

/-!
# Fixed-prime amplitude asymptotic

The exact all-conductor expansion retains a prime-dependent uniform
constant in the error as the exponent tends to infinity.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimePowerAmplitude

open scoped BigOperators Classical
open Filter
open CollisionJordanVariance CollisionConductorArithmetic CollisionUniformAmplitude
open CollisionAmplitudeArithmetic CollisionHarmonicSeed CollisionZetaMoments

theorem rho_prime_power {p a : ℕ} (hp : p.Prime) (ha : a≠0) : rho (p^a)=rho p := by
  rw [rho_euler_product (pow_ne_zero _ hp.ne_zero),rho_euler_product hp.ne_zero,
    Nat.primeFactors_prime_pow ha hp,hp.primeFactors]

theorem nu_prime_power {p a : ℕ} (hp : p.Prime) (ha : a≠0) :
    nu (p^a)=Real.log p/((p : ℝ)-1) := by
  rw [nu,Nat.primeFactors_prime_pow ha hp,Finset.sum_singleton]

theorem delta_prime_power {p a : ℕ} (hp : p.Prime) (ha : a≠0) :
    deltaThree (p^a)=deltaThree p := by
  simp only [deltaThree,Nat.primeFactors_prime_pow ha hp,hp.primeFactors]

theorem amplitude_prime_power_formula {p a : ℕ} (hp : p.Prime) (ha : a≠0) :
    amplitude (p^a)=amplitudeLeading*rho p/(p : ℝ)^(2*a)*
      ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1))+amplitudeError (p^a) := by
  have hpa : 2 ≤ p^a := hp.two_le.trans (le_self_pow hp.one_lt.le ha)
  rw [amplitude_uniform_formula hpa,rho_prime_power hp ha,nu_prime_power hp ha,
    Nat.cast_pow,Real.log_pow,← pow_mul,Nat.mul_comm a 2]

def primeErrorFactor (p : ℕ) : ℝ :=
  zetaNat 4*((p : ℝ)+1)/(12*zetaThree*deltaThree p)

theorem primeErrorFactor_pos (p : ℕ) : 0 < primeErrorFactor p := by
  unfold primeErrorFactor
  positivity [zetaNat_pos (by norm_num : 1<(4 : ℕ)),zetaThree_pos,deltaThree_pos p]

theorem amplitude_prime_power_error {p a : ℕ} (hp : p.Prime) (ha : a≠0) :
    |amplitudeError (p^a)| ≤ primeErrorFactor p/(p : ℝ)^(4*a) := by
  have h := amplitude_uniform_error (q := p^a) (Nat.pow_pos hp.pos)
  rw [delta_prime_power hp ha,Nat.primeFactors_prime_pow ha hp,Finset.prod_singleton,
    Nat.cast_pow,← pow_mul,Nat.mul_comm a 4] at h
  convert! h using 1
  unfold primeErrorFactor
  ring

theorem amplitude_prime_power_asymptotic {p : ℕ} (hp : p.Prime) :
    Asymptotics.IsBigO atTop
      (fun a : ℕ => amplitude (p^a)-amplitudeLeading*rho p/(p : ℝ)^(2*a)*
        ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1)))
      (fun a : ℕ => 1/(p : ℝ)^(4*a)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨primeErrorFactor p,?_⟩
  filter_upwards [eventually_ge_atTop 1] with a ha
  have ha0 : a≠0 := by omega
  rw [amplitude_prime_power_formula hp ha0,add_sub_cancel_left,Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1/(p : ℝ)^(4*a))]
  simpa only [mul_one_div] using amplitude_prime_power_error hp ha0

end NField.Alignment.CollisionPrimePowerAmplitude
