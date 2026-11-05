/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorEndpoint

/-!
# Amplitude asymptotic along the primes

The all-conductor expansion specializes to the exact prime factors. The
resulting inverse-square error has one constant independent of the prime;
no prime number theorem or prime-gap hypothesis enters this estimate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeAmplitudeAsymptotic

open scoped BigOperators Classical
open Filter
open CollisionJordanVariance CollisionConductorArithmetic CollisionZetaMoments
open CollisionSpectralErrorBound CollisionSpectralEnergyError CollisionAmplitudeTail

theorem rho_prime {p : ℕ} (hp : p.Prime) :
    rho p=(p : ℝ)^2/((p : ℝ)^2+(p : ℝ)+1) := by
  rw [rho_euler_product hp.ne_zero,hp.primeFactors,Finset.prod_singleton]

theorem rho_prime_defect_bound {p : ℕ} (hp : p.Prime) :
    |rho p-1| ≤ 1/(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hden : 0 < (p : ℝ)^2+(p : ℝ)+1 := by positivity
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (rho_le_one hp.pos)),rho_prime hp]
  have he : 1-(p : ℝ)^2/((p : ℝ)^2+(p : ℝ)+1)=
      ((p : ℝ)+1)/((p : ℝ)^2+(p : ℝ)+1) := by
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ hden hpR).mpr
  nlinarith

theorem nu_prime (p : ℕ) (hp : p.Prime) : nu p=Real.log p/((p : ℝ)-1) := by
  rw [nu,hp.primeFactors,Finset.sum_singleton]

theorem nu_prime_le_one {p : ℕ} (hp : p.Prime) : nu p ≤ 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [nu_prime p hp]
  apply (div_le_one (by linarith : (0 : ℝ) < (p : ℝ)-1)).mpr
  exact Real.log_le_sub_one_of_pos (by linarith)

theorem residualAmplitude_prime_bound {p : ℕ} (hp : p.Prime) :
    |residualAmplitude p| ≤ (residualConstant+amplitudeLeading)/(p : ℝ)^2 := by
  apply (residualAmplitude_bound hp.two_le).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left (nu_prime_le_one hp) spectralLeading_pos.le
  linarith

theorem rho_prime_log_bound {p : ℕ} (hp : p.Prime) :
    |rho p-1| *Real.log p ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : Real.log (p : ℝ) ≤ (p : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hpR]
  calc
    _ ≤ (1/(p : ℝ))*Real.log p :=
      mul_le_mul_of_nonneg_right (rho_prime_defect_bound hp) (Real.log_natCast_nonneg p)
    _ ≤ (1/(p : ℝ))*(p : ℝ) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 1 := by field_simp

theorem leadingAmplitude_prime_error {p : ℕ} (hp : p.Prime) :
    |leadingAmplitude p-amplitudeLeading*Real.log p/(p : ℝ)^2| ≤ amplitudeLeading/(p : ℝ)^2 := by
  have he : leadingAmplitude p-amplitudeLeading*Real.log p/(p : ℝ)^2=
      amplitudeLeading*(rho p-1)*Real.log p/(p : ℝ)^2 := by
    unfold leadingAmplitude
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_of_pos spectralLeading_pos,
    abs_of_nonneg (Real.log_natCast_nonneg p),abs_of_nonneg (sq_nonneg (p : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left (rho_prime_log_bound hp) spectralLeading_pos.le
  simpa only [mul_assoc,mul_one] using h

theorem amplitude_prime_main_error {p : ℕ} (hp : p.Prime) :
    |amplitude p-amplitudeLeading*Real.log p/(p : ℝ)^2| ≤ amplitudeLogConstant/(p : ℝ)^2 := by
  have h := abs_sub_le (amplitude p) (leadingAmplitude p)
    (amplitudeLeading*Real.log p/(p : ℝ)^2)
  change _ ≤ |residualAmplitude p|+_ at h
  have hb := add_le_add (residualAmplitude_prime_bound hp) (leadingAmplitude_prime_error hp)
  apply h.trans
  convert! hb using 1
  unfold amplitudeLogConstant
  ring

theorem prime_limit_neBot :
    Filter.NeBot (Filter.comap (fun p : Nat.Primes => p.val) atTop) := by
  apply Filter.comap_neBot
  intro t ht
  obtain ⟨N,hN⟩ := Filter.mem_atTop_sets.mp ht
  obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes N
  exact ⟨⟨p,hp⟩,hN p hNp⟩

theorem amplitude_prime_asymptotic :
    Asymptotics.IsBigO (Filter.comap (fun p : Nat.Primes => p.val) atTop)
      (fun p : Nat.Primes => amplitude p.val-amplitudeLeading*Real.log p.val/(p.val : ℝ)^2)
      (fun p : Nat.Primes => 1/(p.val : ℝ)^2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨amplitudeLogConstant,Filter.Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0 ≤ 1/(p.val : ℝ)^2)]
  simpa only [mul_one_div] using amplitude_prime_main_error p.property

end NField.Alignment.CollisionPrimeAmplitudeAsymptotic
