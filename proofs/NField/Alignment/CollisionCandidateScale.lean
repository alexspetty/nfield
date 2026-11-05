/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorCosts
import NField.Alignment.CollisionPrimeDistribution
import NField.Alignment.CollisionPrimeAmplitudeAsymptotic

/-!
# Uniform comparison of prime candidates with excluded coordinate costs

The prime number theorem supplies an actual prime near every large cutoff.
Its full-amplitude bound gives a uniform upper bound for the restricted gap.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCandidateScale

open scoped BigOperators Topology
open Filter Asymptotics
open CollisionConductorCosts CollisionPrimeDistribution CollisionPrimeAmplitudeAsymptotic
open CollisionPrimeCandidate CollisionRestrictedGap CollisionJordanVariance
open CollisionZetaMoments CollisionDivisorSeries CollisionPositiveConstants
open CollisionSpectralEnergyError CollisionAmplitudeTail

theorem amplitudeLeading_eq_real_zeta_ratio : amplitudeLeading=realZeta 2/realZeta 3 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div,realZeta_eq_riemannZeta (by norm_num : (1 : ℝ) < 2),
    realZeta_eq_riemannZeta (by norm_num : (1 : ℝ) < 3),amplitudeLeading_eq_zeta_ratio]
  norm_num

theorem amplitudeLeading_lt_three_halves : amplitudeLeading < (3/2 : ℝ) := by
  have hz3 := realZeta_three_lower
  have hz2 : realZeta 2 < (9/5 : ℝ) := by
    rw [realZeta_two]
    nlinarith [Real.pi_pos,Real.pi_lt_d2]
  rw [amplitudeLeading_eq_real_zeta_ratio]
  apply (div_lt_iff₀ (by linarith : 0 < realZeta 3)).mpr
  nlinarith

theorem prime_candidate_scale_bound {Q p : ℕ} (hp : Nat.Prime p) (hpQ : p ≤ Q)
    (hnear : (9/10 : ℝ)*(Q : ℝ) ≤ (p : ℝ)) :
    (2/3 : ℝ)*amplitude p ≤
      ((100/81 : ℝ)*Real.log Q+(200/243 : ℝ)*amplitudeLogConstant)/(Q : ℝ)^2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQ : 0 < Q := lt_of_lt_of_le hp.pos hpQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpQR : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
  have hlog := Real.log_le_log hpR hpQR
  have hlogQ := Real.log_natCast_nonneg Q
  have hA := amplitudeLeading_lt_three_halves
  have hleft := mul_le_mul_of_nonneg_left hlog spectralLeading_pos.le
  have hright := mul_le_mul_of_nonneg_right hA.le hlogQ
  have hterm : amplitudeLeading*Real.log p ≤ (3/2 : ℝ)*Real.log Q := hleft.trans hright
  have herr := (abs_le.mp (amplitude_prime_main_error hp)).2
  have hdiv := div_le_div_of_nonneg_right hterm (sq_nonneg (p : ℝ))
  have hnum : amplitude p ≤ ((3/2 : ℝ)*Real.log Q+amplitudeLogConstant)/(p : ℝ)^2 := by
    rw [add_div]
    linarith
  have hn : 0 ≤ (3/2 : ℝ)*Real.log Q+amplitudeLogConstant := by
    have := amplitudeLogConstant_pos
    positivity
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (9/10 : ℝ)*(Q : ℝ)) hnear
  have hden : (81/100 : ℝ)*(Q : ℝ)^2 ≤ (p : ℝ)^2 := by nlinarith
  have hb := hnum.trans (div_le_div_of_nonneg_left hn (by positivity) hden)
  have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2/3)
  convert! h using 1
  field_simp
  ring

theorem candidate_error_absorbed :
    ∀ᶠ Q : ℕ in atTop, (100/81 : ℝ)*Real.log Q+(200/243 : ℝ)*amplitudeLogConstant ≤
      (5/4 : ℝ)*Real.log Q := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ht.eventually (eventually_ge_atTop ((160/3 : ℝ)*amplitudeLogConstant))
  filter_upwards [h] with Q hQ
  change (160/3 : ℝ)*amplitudeLogConstant ≤ Real.log Q at hQ
  linarith

theorem eventual_prime_candidate_upper :
    ∀ᶠ Q : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ p ≤ Q ∧ Q < 2*p ∧
      (2/3 : ℝ)*amplitude p ≤ (5/4 : ℝ)*Real.log Q/(Q : ℝ)^2 := by
  have hp := prime_in_relative_interval_nat (c := (9/10 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hp,candidate_error_absorbed,eventually_ge_atTop (1 : ℕ)] with Q hQ herror hQ1
  obtain ⟨p,hpp,hnear,hpQ⟩ := hQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have htop : Q < 2*p := by
    have ht : (Q : ℝ) < 2*(p : ℝ) := by linarith
    exact_mod_cast ht
  refine ⟨p,hpp,hpQ,htop,?_⟩
  exact (prime_candidate_scale_bound hpp hpQ hnear.le).trans
    (div_le_div_of_nonneg_right herror (sq_nonneg _))

theorem restrictedGap_upper_scale :
    ∀ᶠ Q : ℕ in atTop, restrictedGap Q ≤ (5/4 : ℝ)*Real.log Q/(Q : ℝ)^2 := by
  filter_upwards [eventual_prime_candidate_upper,eventually_ge_atTop (3 : ℕ)] with Q hQ hQ3
  obtain ⟨p,hp,hpQ,htop,hcost⟩ := hQ
  exact (restrictedGap_le_prime hQ3 hp hpQ htop).trans hcost

theorem small_prime_scale_separated :
    ∀ᶠ Q : ℕ in atTop, restrictedGap Q <
      (4/3 : ℝ)*Real.log ((Q : ℝ)/2)/(Q : ℝ)^2 := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := ht.eventually (eventually_gt_atTop (16*Real.log 2))
  filter_upwards [restrictedGap_upper_scale,hlog,eventually_ge_atTop (1 : ℕ)] with Q hQ hL hQ1
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  apply hQ.trans_lt
  apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hQR)).mpr
  rw [Real.log_div hQR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  change 16*Real.log 2 < Real.log Q at hL
  linarith

theorem eventual_minimizer_small_primes :
    ∀ᶠ Q : ℕ in atTop, ∀ a : ℕ, conductorGap Q a=restrictedGap Q →
      ∀ p : ℕ, p.Prime → 2*p ≤ Q → p ∣ a := by
  filter_upwards [small_prime_scale_separated] with Q hQ
  intro a ha p hp hpQ
  by_contra hpa
  have hcost := conductorGap_small_prime_lower hp hpQ hpa
  rw [ha] at hcost
  linarith

theorem candidate_lt_higher_power_scale {Q : ℕ} (hQ : 100 ≤ Q) :
    (5/4 : ℝ)*Real.log Q/(Q : ℝ)^2 <
      Real.log Q/(6*(Q : ℝ)^((3 : ℝ)/2)) := by
  have hQR : (100 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < Q := by linarith
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hsqrt : (15/2 : ℝ) < Real.sqrt Q := Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hsqrt0 := Real.sqrt_pos.2 hpos
  have hsquare := Real.sq_sqrt hpos.le
  have hbase : (15/2 : ℝ)*Real.sqrt Q < (Q : ℝ) := by
    nlinarith [mul_pos hsqrt0 (sub_pos.mpr hsqrt)]
  rw [show (3 : ℝ)/2=1+1/2 by norm_num,Real.rpow_add hpos,
    Real.rpow_one,← Real.sqrt_eq_rpow]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hpos) (by positivity)).mpr
  have h := mul_lt_mul_of_pos_left hbase (mul_pos hlog hpos)
  nlinarith

theorem higher_power_scale_separated :
    ∀ᶠ Q : ℕ in atTop, restrictedGap Q <
      Real.log Q/(6*(Q : ℝ)^((3 : ℝ)/2)) := by
  filter_upwards [restrictedGap_upper_scale,eventually_ge_atTop (100 : ℕ)] with Q hQ hQ100
  exact hQ.trans_lt (candidate_lt_higher_power_scale hQ100)

theorem eventual_minimizer_higher_powers :
    ∀ᶠ Q : ℕ in atTop, ∀ a : ℕ, conductorGap Q a=restrictedGap Q →
      ∀ p j : ℕ, p.Prime → 1 ≤ j → p^(j+1) ≤ Q → p^j ∣ a → p^(j+1) ∣ a := by
  filter_upwards [higher_power_scale_separated] with Q hQ
  intro a ha p j hp hj hpQ hprev
  by_contra hmiss
  have hcost := conductorGap_higher_power_lower hp hj hpQ hprev hmiss
  rw [ha] at hcost
  linarith

end NField.Alignment.CollisionCandidateScale
