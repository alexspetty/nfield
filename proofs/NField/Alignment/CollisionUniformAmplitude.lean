/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorArithmetic
import NField.Alignment.CollisionHarmonicSeedExpansion
import NField.Alignment.CollisionAmplitudeRefinement
import NField.Alignment.CollisionMassInverse

/-!
# The uniform conductor expansion

The actual full amplitudes satisfy the manuscript's expansion with its
literal uniform error factor. The seed remainder, finite Mobius cancellation
and every constant identification are proved inputs, not assumptions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionUniformAmplitude

open scoped BigOperators Classical
open ArithmeticFunction CollisionAmplitudeArithmetic CollisionAmplitudeRefinement
open CollisionHarmonicSeed CollisionZetaMoments CollisionHarmonicSeedExpansion
open CollisionConductorArithmetic CollisionSquarefreeEuler CollisionJordanVariance

def amplitudeError (q : ℕ) : ℝ := 1/(zetaThree*deltaThree q)*
  ∑ d ∈ q.divisors, (moebius d : ℝ)/(d : ℝ)^3*seedError (q/d)

theorem refinement_expansion_term {q d : ℕ} (hq : 0<q) (hd : d∈q.divisors) :
    (moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d)=
      (zetaNat 2/(q : ℝ)^2)*
        ((Real.log q+kappaZero)*((moebius d : ℝ)/(d : ℝ))-
          (moebius d : ℝ)*Real.log d/(d : ℝ))-
      (zetaThree/(2*(q : ℝ)^3))*(moebius d : ℝ)+
      (moebius d : ℝ)/(d : ℝ)^3*seedError (q/d) := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hdiv := Nat.div_pos (Nat.le_of_dvd hq hdvd) (Nat.pos_of_mem_divisors hd)
  rw [harmonicSeed_expansion hdiv,Nat.cast_div hdvd hdR,Real.log_div hqR hdR]
  field_simp
  ring

theorem amplitude_uniform_formula {q : ℕ} (hq : 2≤q) :
    amplitude q=amplitudeLeading*rho q/(q : ℝ)^2*
      (Real.log q+kappaZero+nu q)+amplitudeError q := by
  have hq0 : q≠0 := by omega
  have hq1 : q≠1 := by omega
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq0
  have hz := zetaThree_pos.ne'
  have hdelta := (deltaThree_pos q).ne'
  have he : (∑ d ∈ q.divisors, (moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d))=
      (zetaNat 2/(q : ℝ)^2)*
        ((Real.log q+kappaZero)*totientRatio q+totientRatio q*nu q)+
      ∑ d ∈ q.divisors, (moebius d : ℝ)/(d : ℝ)^3*seedError (q/d) := by
    calc
      _ = ∑ d ∈ q.divisors,
          ((zetaNat 2/(q : ℝ)^2)*
            ((Real.log q+kappaZero)*((moebius d : ℝ)/(d : ℝ))-
              (moebius d : ℝ)*Real.log d/(d : ℝ))-
          (zetaThree/(2*(q : ℝ)^3))*(moebius d : ℝ)+
          (moebius d : ℝ)/(d : ℝ)^3*seedError (q/d)) :=
        Finset.sum_congr rfl (fun _ hd => refinement_expansion_term (by omega) hd)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
          ← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,
          moebius_divisor_inverse hq0,moebius_log_divisor hq0,
          CollisionMassInverse.moebius_divisor_sum,if_neg hq1]
        ring
  rw [amplitude_exact_transform (by omega),he,amplitudeError,amplitudeLeading,rho]
  field_simp

theorem seedError_abs_bound {q : ℕ} (hq : 0<q) :
    |seedError q|≤zetaNat 4/(12*(q : ℝ)^4) := by
  have he := seedError_bounds hq
  rw [abs_of_neg he.2]
  linarith

theorem amplitude_error_term_bound {q d : ℕ} (hq : 0<q) (hd : d∈q.divisors) :
    |(moebius d : ℝ)/(d : ℝ)^3*seedError (q/d)|≤
      (zetaNat 4/(12*(q : ℝ)^4))*(|(moebius d : ℝ)| *(d : ℝ)) := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hdpos.ne'
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hdiv := Nat.div_pos (Nat.le_of_dvd hq hdvd) hdpos
  rw [abs_mul,abs_div,abs_of_nonneg (by positivity : 0≤(d : ℝ)^3)]
  calc
    _ ≤ (|(moebius d : ℝ)| /(d : ℝ)^3)*(zetaNat 4/(12*((q/d : ℕ) : ℝ)^4)) := by
      exact mul_le_mul_of_nonneg_left (seedError_abs_bound hdiv) (by positivity)
    _ = _ := by
      rw [Nat.cast_div hdvd hdR]
      field_simp

theorem amplitude_uniform_error {q : ℕ} (hq : 0<q) :
    |amplitudeError q|≤zetaNat 4/(12*zetaThree*(q : ℝ)^4*deltaThree q)*
      ∏ p ∈ q.primeFactors, ((p : ℝ)+1) := by
  have hz := zetaThree_pos.ne'
  have hd := (deltaThree_pos q).ne'
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hc : 0<1/(zetaThree*deltaThree q) :=
    one_div_pos.mpr (mul_pos zetaThree_pos (deltaThree_pos q))
  rw [amplitudeError,abs_mul,abs_of_pos hc]
  calc
    _ ≤ 1/(zetaThree*deltaThree q)*
        ∑ d ∈ q.divisors, |(moebius d : ℝ)/(d : ℝ)^3*seedError (q/d)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc.le
    _ ≤ 1/(zetaThree*deltaThree q)*
        ∑ d ∈ q.divisors, (zetaNat 4/(12*(q : ℝ)^4))*(|(moebius d : ℝ)| *(d : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact Finset.sum_le_sum (fun _ hd => amplitude_error_term_bound hq hd)
    _ = _ := by
      rw [← Finset.mul_sum,abs_moebius_divisor_product hq.ne']
      field_simp

theorem amplitude_prime_exact {p : ℕ} (hp : p.Prime) :
    amplitude p=(harmonicSeed p-(1/(p : ℝ)^3)*harmonicSeed 1)/
      (zetaThree*(1-((p : ℝ)^3)⁻¹)) := by
  have hz := zetaThree_pos.ne'
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp.ne_zero
  have hd : 1-((p : ℝ)^3)⁻¹≠0 := by
    have he := deltaThree_pos p
    simpa only [deltaThree,hp.primeFactors,Finset.prod_singleton] using he.ne'
  rw [amplitude_exact_transform hp.pos,deltaThree,hp.primeFactors,
    Finset.prod_singleton,hp.divisors]
  simp only [Finset.sum_pair hp.ne_one.symm,Nat.div_one,Nat.div_self hp.pos]
  norm_num [moebius_apply_prime hp]
  field_simp
  ring

theorem uniform_conductor_expansion {q : ℕ} (hq : 2≤q) :
    amplitude q=amplitudeLeading*rho q/(q : ℝ)^2*
      (Real.log q+kappaZero+nu q)+amplitudeError q ∧
    |amplitudeError q|≤zetaNat 4/(12*zetaThree*(q : ℝ)^4*deltaThree q)*
      (∏ p ∈ q.primeFactors, ((p : ℝ)+1)) ∧
    (amplitudeLeading : ℂ)=riemannZeta 2/riemannZeta 3 ∧
    (kappaZero : ℂ)=(Real.eulerMascheroniConstant : ℂ)-deriv riemannZeta 2/riemannZeta 2 ∧
    (zetaNat 4 : ℂ)=riemannZeta 4 := by
  refine ⟨amplitude_uniform_formula hq,amplitude_uniform_error (by omega),
    amplitudeLeading_eq_zeta_ratio,kappaZero_eq_zeta_derivative,?_⟩
  have he := zetaNat_eq_riemannZeta (by norm_num : 1<(4 : ℕ))
  norm_num only [Nat.cast_ofNat] at he
  exact he

end NField.Alignment.CollisionUniformAmplitude
