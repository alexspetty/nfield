/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLargestPrime
import NField.Alignment.CollisionMinimizerClassification

/-!
# The sharp asymptotic of the restricted conductor gap

The full prime amplitudes have a uniform inverse-square error. Their
minimum is squeezed between a uniform lower bound and the amplitude at
the actual largest prime below the cutoff. No finite experiment enters
the limit or the eventual exact minimum formula.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRestrictedGapAsymptotic

open scoped BigOperators Classical
open Filter Asymptotics
open CollisionLargestPrime CollisionMinimizerClassification CollisionCandidateScale
open CollisionRestrictedGap CollisionPrimeAmplitudeAsymptotic CollisionConductorCosts
open CollisionJordanVariance CollisionZetaMoments CollisionSpectralEnergyError CollisionAmplitudeTail

theorem amplitude_prime_normalized_error {p : ℕ} (hp : p.Prime) :
    |amplitude p*(p : ℝ)^2/Real.log p-amplitudeLeading| ≤ amplitudeLogConstant/Real.log p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have he : amplitude p*(p : ℝ)^2/Real.log p-amplitudeLeading=
      (amplitude p-amplitudeLeading*Real.log p/(p : ℝ)^2)*((p : ℝ)^2/Real.log p) := by
    field_simp
  rw [he,abs_mul,abs_of_pos (div_pos (sq_pos_of_pos hpR) hlog)]
  have h := mul_le_mul_of_nonneg_right (amplitude_prime_main_error hp)
    (div_pos (sq_pos_of_pos hpR) hlog).le
  convert! h using 1
  field_simp

theorem largestPrime_amplitude_normalized_tendsto :
    Tendsto (fun Q : ℕ => amplitude (largestPrime Q)*(largestPrime Q : ℝ)^2/
      Real.log (largestPrime Q)) atTop (nhds amplitudeLeading) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have ht := Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp largestPrime_tendsto)
  have hlim : Tendsto (fun Q : ℕ => amplitudeLogConstant/Real.log (largestPrime Q))
      atTop (nhds 0) := by
    simpa only [mul_zero,div_eq_mul_inv,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp ht).const_mul amplitudeLogConstant
  refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  exact amplitude_prime_normalized_error (largestPrime_prime hQ)

theorem largestPrime_amplitude_at_cutoff_tendsto :
    Tendsto (fun Q : ℕ => amplitude (largestPrime Q)*(Q : ℝ)^2/Real.log Q)
      atTop (nhds amplitudeLeading) := by
  have h := (largestPrime_amplitude_normalized_tendsto.mul log_largestPrime_ratio_tendsto).mul
    ((largestPrime_ratio_tendsto.inv₀ (by norm_num)).pow 2)
  simp only [inv_one,one_pow,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hp := largestPrime_prime hQ
  have hpR : (0 : ℝ) < largestPrime Q := by exact_mod_cast hp.pos
  have hQR : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  have hlogp := (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < largestPrime Q)).ne'
  have hlogQ := (Real.log_pos hQR).ne'
  field_simp

theorem top_prime_amplitude_lower {Q p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) (htop : Q < 2*p) :
    (amplitudeLeading*Real.log Q-4*amplitudeLogConstant)/(Q : ℝ)^2 ≤ amplitude p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le hp.pos hpQ)
  have hpQR : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx := exp_half_le_two.trans hp2
  have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 2)
    hx (hx.trans hpQR) hpQR
  simp only [Real.rpow_two] at hmono
  have hmain := mul_le_mul_of_nonneg_left hmono spectralLeading_pos.le
  have htopR : (Q : ℝ) ≤ 2*(p : ℝ) := by exact_mod_cast htop.le
  have hsq : (Q : ℝ)^2 ≤ 4*(p : ℝ)^2 := by nlinarith
  have hC := amplitudeLogConstant_pos.le
  have herr : amplitudeLogConstant/(p : ℝ)^2 ≤ 4*amplitudeLogConstant/(Q : ℝ)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hpR) (sq_pos_of_pos hQR)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  have hamp := (abs_le.mp (amplitude_prime_main_error hp)).1
  rw [sub_div]
  rw [← mul_div_assoc,← mul_div_assoc] at hmain
  linarith

theorem topPrimeAmplitude_attained {Q : ℕ} (hQ : (topPrimes Q).Nonempty) :
    ∃ p ∈ topPrimes Q, topPrimeAmplitude Q=amplitude p := by
  rw [topPrimeAmplitude,dif_pos hQ]
  exact Finset.exists_mem_eq_inf' hQ amplitude

theorem eventual_topPrimeAmplitude_bounds :
    ∀ᶠ Q : ℕ in atTop,
      (amplitudeLeading*Real.log Q-4*amplitudeLogConstant)/(Q : ℝ)^2 ≤ topPrimeAmplitude Q ∧
      topPrimeAmplitude Q ≤ amplitude (largestPrime Q) := by
  filter_upwards [largestPrime_eventually_top] with Q hQ
  have hm : largestPrime Q ∈ topPrimes Q := topPrimes_mem.mpr hQ
  obtain ⟨p,hp,hvalue⟩ := topPrimeAmplitude_attained ⟨largestPrime Q,hm⟩
  have hp' := topPrimes_mem.mp hp
  refine ⟨?_,topPrimeAmplitude_le hm⟩
  rw [hvalue]
  exact top_prime_amplitude_lower hp'.1 hp'.2.1 hp'.2.2

theorem topPrimeAmplitude_normalized_tendsto :
    Tendsto (fun Q : ℕ => topPrimeAmplitude Q*(Q : ℝ)^2/Real.log Q)
      atTop (nhds amplitudeLeading) := by
  have hinvLog := tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlo : Tendsto (fun Q : ℕ => amplitudeLeading-4*amplitudeLogConstant/Real.log Q)
      atTop (nhds amplitudeLeading) := by
    simpa only [div_eq_mul_inv,mul_zero,sub_zero,Function.comp_def] using
      tendsto_const_nhds.sub (hinvLog.const_mul (4*amplitudeLogConstant))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo largestPrime_amplitude_at_cutoff_tendsto
  · filter_upwards [eventual_topPrimeAmplitude_bounds,eventually_ge_atTop (2 : ℕ)] with Q hb hQ
    have hQR : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
    have hlog := Real.log_pos hQR
    have hQ0 : (Q : ℝ) ≠ 0 := by linarith
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb.1 (sq_nonneg (Q : ℝ))) hlog.le
    convert! h using 1
    field_simp
  · filter_upwards [eventual_topPrimeAmplitude_bounds,eventually_ge_atTop (2 : ℕ)] with Q hb hQ
    have hlog : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb.2 (sq_nonneg (Q : ℝ))) hlog

theorem restrictedGap_normalized_tendsto :
    Tendsto (fun Q : ℕ => restrictedGap Q*(Q : ℝ)^2/Real.log Q)
      atTop (nhds ((2/3 : ℝ)*amplitudeLeading)) := by
  have h := topPrimeAmplitude_normalized_tendsto.const_mul (2/3 : ℝ)
  apply h.congr'
  filter_upwards [eventual_restricted_gap_exact] with Q hQ
  rw [hQ]
  ring

theorem restrictedGap_asymptotic :
    restrictedGap ~[atTop]
      (fun Q : ℕ => (2/3 : ℝ)*amplitudeLeading*Real.log Q/(Q : ℝ)^2) := by
  apply isEquivalent_of_tendsto_one
  have hA : (2/3 : ℝ)*amplitudeLeading ≠ 0 :=
    (mul_pos (by norm_num) spectralLeading_pos).ne'
  have h := restrictedGap_normalized_tendsto.div_const ((2/3 : ℝ)*amplitudeLeading)
  rw [div_self hA] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hQR : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  have hlog := (Real.log_pos hQR).ne'
  have hQ0 : (Q : ℝ) ≠ 0 := by linarith
  change restrictedGap Q*(Q : ℝ)^2/Real.log Q/((2/3 : ℝ)*amplitudeLeading)=
    restrictedGap Q/((2/3 : ℝ)*amplitudeLeading*Real.log Q/(Q : ℝ)^2)
  field_simp

theorem restrictedGap_literal_asymptotic :
    restrictedGap ~[atTop]
      (fun Q : ℕ => (2*CollisionDivisorSeries.realZeta 2/(3*CollisionDivisorSeries.realZeta 3))*
        Real.log Q/(Q : ℝ)^2) := by
  have h := restrictedGap_asymptotic
  rw [amplitudeLeading_eq_real_zeta_ratio] at h
  convert! h using 1
  funext Q
  ring

theorem restrictedGap_two_sided_order :
    restrictedGap =Θ[atTop] (fun Q : ℕ => Real.log Q/(Q : ℝ)^2) := by
  have h := restrictedGap_asymptotic.isTheta
  have hA : (2/3 : ℝ)*amplitudeLeading ≠ 0 :=
    (mul_pos (by norm_num) spectralLeading_pos).ne'
  have he : (fun Q : ℕ => (2/3 : ℝ)*amplitudeLeading*Real.log Q/(Q : ℝ)^2)=
      (fun Q : ℕ => ((2/3 : ℝ)*amplitudeLeading)*(Real.log Q/(Q : ℝ)^2)) := by
    funext Q
    ring
  rw [he] at h
  exact h.of_const_mul_right hA

end NField.Alignment.CollisionRestrictedGapAsymptotic
