/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FiniteFourier
import NField.ResetForests.Targets
import NField.Alignment.CommonResetFourier
import NField.Alignment.CommonResetBernoulliLifts
/-! # The sharp complete-clock row

The full multiplication orbit includes every nonunit frequency. Reflection
pays the printed harmonic factor at half the modulus, rather than at the
whole modulus.
-/

noncomputable section

namespace NField.ResetForests.ClockRows

open scoped BigOperators
open NField.Alignment
open DedekindFourierMoment DedekindReciprocity CarryBoundarySpectra
open CommonResetFourier RademacherThreeTerm

theorem circular_reciprocal_half_harmonic {m : ℕ} (_hm : 0 < m) :
    (∑ n ∈ Finset.Ico 1 m, 1/(circularDistance m n : ℝ)) ≤
      2*(harmonic (m/2) : ℝ) := by
  classical
  let f := fun n : ℕ => if n ≤ m/2 then 1/(n : ℝ) else 0
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have href : (∑ n ∈ Finset.Ico 1 m, f (m-n)) = ∑ n ∈ Finset.Ico 1 m, f n := by
    simpa using Finset.sum_Ico_reflect f 1 (by omega : m ≤ m+1)
  have hsum : (∑ n ∈ Finset.Ico 1 m, f n) = (harmonic (m/2) : ℝ) := by
    change (∑ n ∈ Finset.Ico 1 m, if n ≤ m/2 then 1/(n : ℝ) else 0)=_
    rw [← Finset.sum_filter]
    have hset : (Finset.Ico 1 m).filter (fun n => n ≤ m/2) = Finset.Icc 1 (m/2) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_eq_sum_Icc (n := m/2))
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using hcast.symm
  calc
    _ ≤ ∑ n ∈ Finset.Ico 1 m, (f n+f (m-n)) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnm⟩ := Finset.mem_Ico.mp hn
      by_cases hle : n ≤ m-n
      · have hhalf : n ≤ m/2 := by omega
        rw [circularDistance, min_eq_left hle]
        exact le_add_of_le_of_nonneg (by simp [f, hhalf]) (hf0 _)
      · have hhalf : m-n ≤ m/2 := by omega
        rw [circularDistance, min_eq_right (by omega : m-n ≤ n)]
        exact le_add_of_nonneg_of_le (hf0 _) (by simp [f, hhalf])
    _ = (∑ n ∈ Finset.Ico 1 m, f n)+(∑ n ∈ Finset.Ico 1 m, f (m-n)) :=
      Finset.sum_add_distrib
    _ = _ := by rw [href, hsum]; ring

theorem frequency_envelope_half_mass {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Finset.range q, frequencyEnvelope q r) ≤
      (q : ℝ)*(harmonic (q/2) : ℝ)/2 := by
  rw [sum_range_eq_sum_Ico_one (frequencyEnvelope q) hq (by simp [frequencyEnvelope])]
  calc
    _ = ((q : ℝ)/4)*(∑ r ∈ Finset.Ico 1 q, 1/(circularDistance q r : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr0 : r ≠ 0 := by have := (Finset.mem_Ico.mp hr).1; omega
      rw [frequencyEnvelope, if_neg hr0]
      ring
    _ ≤ ((q : ℝ)/4)*(2*(harmonic (q/2) : ℝ)) := by
      gcongr
      exact circular_reciprocal_half_harmonic hq
    _ = _ := by ring

theorem sawtooth_fourier_half_mass {m : ℕ} (hm : 0 < m) :
    sawtoothFourierNormMass m ≤ (m : ℝ)*(harmonic (m/2) : ℝ)/2 := by
  unfold sawtoothFourierNormMass
  calc
    _ ≤ ∑ r ∈ Finset.range m, frequencyEnvelope m r := by
      apply Finset.sum_le_sum
      intro r hr
      simpa using norm_scaled_sawtoothFourier_le_envelope
        (d := 1) (by decide) hm (Finset.mem_range.mp hr)
    _ ≤ _ := frequency_envelope_half_mass hm

theorem sawtooth_fourier_half_orbit {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∑ j ∈ Finset.range m, ‖sawtoothFourier m ((n*j)%m)‖) ≤
      (m : ℝ)*(harmonic (m/2) : ℝ)/2 := by
  let d := n.gcd m
  let q := m/d
  let h := n/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left m hn
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hq : 0 < q := Nat.div_pos (Nat.gcd_le_right n hm) hd
  have hmfac : m=d*q := (Nat.mul_div_cancel' hdm).symm
  have hnfac : n=d*h := (Nat.mul_div_cancel' hdn).symm
  have hcop : h.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  rw [sum_mul_mod_of_factorization hd hq hmfac hnfac hcop
    (fun r => ‖sawtoothFourier m r‖), nsmul_eq_mul]
  calc
    _ ≤ (d : ℝ)*(∑ r ∈ Finset.range q, frequencyEnvelope q r) := by
      gcongr with r hr
      rw [hmfac]
      exact norm_scaled_sawtoothFourier_le_envelope hd hq (Finset.mem_range.mp hr)
    _ ≤ (d : ℝ)*((q : ℝ)*(harmonic (q/2) : ℝ)/2) := by
      gcongr
      exact frequency_envelope_half_mass hq
    _ ≤ (d : ℝ)*((q : ℝ)*(harmonic (m/2) : ℝ)/2) := by
      gcongr
      exact_mod_cast harmonic_cast_mono (Nat.div_le_div_right (Nat.div_le_self m d))
    _ = _ := by rw [hmfac]; push_cast; ring

theorem dft_sawtooth_half_orbit {m : ℕ} [NeZero m] (n : ZMod m) :
    (∑ h : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) (h*n)‖) ≤
      (m : ℝ)*(harmonic (m/2) : ℝ)/2 := by
  have hH : (0 : ℝ) ≤ (harmonic (m/2) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (m/2))
  by_cases hn : n=0
  · subst n
    simp only [mul_zero, norm_dft_centeredSawtooth_eq, ZMod.val_zero,
      sawtoothFourier_zero (NeZero.pos m), norm_zero, Finset.sum_const_zero]
    positivity
  · have hn0 : 0 < n.val := ZMod.val_pos.mpr hn
    have he (h : ZMod m) : ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) (h*n)‖ =
        ‖sawtoothFourier m ((n.val*h.val)%m)‖ := by
      rw [norm_dft_centeredSawtooth_eq, ZMod.val_mul, mul_comm]
    simp_rw [he]
    rw [CommonResetBernoulliLifts.sum_residue_values
      (fun h => ‖sawtoothFourier m ((n.val*h)%m)‖)]
    exact sawtooth_fourier_half_orbit (NeZero.pos m) hn0

theorem residue_dedekind_half_row {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (∑ h : ZMod m, ‖residueDedekind h‖) ≤
      (m : ℝ)/4*(harmonic (m/2) : ℝ)^2 := by
  let F := ZMod.dft (centeredSawtooth : ZMod m → ℂ)
  have hH : (0 : ℝ) ≤ (harmonic (m/2) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (m/2))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hmass : (∑ n : ZMod m, ‖F n‖) ≤
      (m : ℝ)*(harmonic (m/2) : ℝ)/2 := by
    change (∑ n : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) n‖)≤_
    rw [dft_centeredSawtooth_normMass_eq]
    exact sawtooth_fourier_half_mass (NeZero.pos m)
  have hpoint (h : ZMod m) : ‖residueDedekind h‖ ≤
      (m : ℝ)⁻¹*(∑ n : ZMod m, ‖F n‖*‖F (h*n)‖) := by
    rw [residueDedekind_fourier hm, norm_mul, norm_neg, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans_eq (by simp only [norm_mul]; rfl)) (by positivity)
  calc
    _ ≤ ∑ h : ZMod m, (m : ℝ)⁻¹*(∑ n : ZMod m, ‖F n‖*‖F (h*n)‖) :=
      Finset.sum_le_sum (fun h _ => hpoint h)
    _ = (m : ℝ)⁻¹*(∑ n : ZMod m, ‖F n‖*(∑ h : ZMod m, ‖F (h*n)‖)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (m : ℝ)⁻¹*(∑ n : ZMod m, ‖F n‖*((m : ℝ)*(harmonic (m/2) : ℝ)/2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left (dft_sawtooth_half_orbit n) (norm_nonneg _)
    _ = (m : ℝ)⁻¹*((∑ n : ZMod m, ‖F n‖)*((m : ℝ)*(harmonic (m/2) : ℝ)/2)) := by
      rw [Finset.sum_mul]
    _ ≤ (m : ℝ)⁻¹*(((m : ℝ)*(harmonic (m/2) : ℝ)/2)*
        ((m : ℝ)*(harmonic (m/2) : ℝ)/2)) := by
      gcongr
    _ = _ := by field_simp; ring

theorem correlation_as_residue {d p : ℕ} [NeZero d] (hd : 0 < d)
    (hpd : p.Coprime d) (a : ℕ) :
    (arithmeticCoefficientDedekindTerm a p d : ℂ) =
      residueDedekind ((ZMod.unitOfCoprime p hpd)⁻¹.val*(a : ZMod d)) := by
  rw [CommonResetBernoulliLifts.coefficient_swap a p d,
    EndpointReciprocityBridge.arithmeticCoefficientDedekindTerm_unit_left hd hpd]
  rw [← residueDedekind_eq_rational]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem complete_clock_row_bound {d p : ℕ} (hd : 2 ≤ d) (hpd : p.Coprime d) :
    (∑ a ∈ Finset.range d, |Core.completeCorrelation p a d|) ≤
      (d : ℝ)/4*(harmonic (d/2) : ℝ)^2 := by
  letI : NeZero d := ⟨by omega⟩
  let u := (ZMod.unitOfCoprime p hpd)⁻¹
  have hpoint (a : ℕ) : |Core.completeCorrelation p a d| =
      ‖residueDedekind (u.val*(a : ZMod d))‖ := by
    have he := correlation_as_residue (by omega : 0 < d) hpd a
    rw [← he]
    simp only [Core.completeCorrelation]
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hpoint]
  have hreindex := Equiv.sum_comp u.mulLeft (fun h : ZMod d => ‖residueDedekind h‖)
  simp only [Units.mulLeft_apply] at hreindex
  have hgrid : (∑ a ∈ Finset.range d, ‖residueDedekind (u.val*(a : ZMod d))‖) =
      ∑ h : ZMod d, ‖residueDedekind h‖ := by
    rw [← CommonResetBernoulliLifts.sum_residue_values
      (fun a => ‖residueDedekind (u.val*(a : ZMod d))‖)]
    simp only [ZMod.natCast_zmod_val]
    exact hreindex
  rw [hgrid]
  exact residue_dedekind_half_row hd

theorem complete_clock_row_estimate : Core.CompleteClockRowEstimate := by
  intro p d hp hd hdp
  apply complete_clock_row_bound hd
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hdp)

end NField.ResetForests.ClockRows
