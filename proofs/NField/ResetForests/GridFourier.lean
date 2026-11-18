/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FiniteFourier
import NField.ResetForests.Schur
import NField.Alignment.DedekindFourierMoment
import NField.Alignment.CommonResetTeeth
import NField.Alignment.CommonResetBernoulliLifts
/-! # The complete reset-grid Fourier matrix

Every multiplication fibre is retained. Its multiplicity is bounded by the
actual gcd, and the full divisor sum pays for all such fibres.
-/

noncomputable section

namespace NField.ResetForests.ResetGrid

open scoped BigOperators
open NField.Alignment
open DedekindFourierMoment CarryBoundarySpectra

variable {k : ℕ} [NeZero k]

theorem multiplication_fibre_card_le (u j : ZMod k) :
    (Finset.univ.filter (fun h : ZMod k => h*u=j)).card ≤ u.val.gcd k := by
  classical
  let s := Finset.univ.filter (fun h : ZMod k => h*u=j)
  let t := Finset.univ.filter (fun h : ZMod k => h*u=0)
  have ht : t.card = u.val.gcd k := by
    have h := CommonResetTeeth.simultaneous_zero_count (m := k) u.val 0
    simpa [t, mul_comm] using h
  change s.card ≤ _
  rw [← ht]
  by_cases hs : s.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hs
    have hh₀' : h₀*u=j := (Finset.mem_filter.mp hh₀).2
    apply Finset.card_le_card_of_injOn (fun h => h-h₀)
    · intro h hh
      have hh' : h*u=j := (Finset.mem_filter.mp hh).2
      change h-h₀ ∈ t
      simp [t, sub_mul, hh', hh₀']
    · intro a _ b _ hab
      exact sub_left_injective hab
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty,
      Nat.zero_le]

theorem multiplication_pushforward_row_bound (F : ZMod k → ℂ) (j : ZMod k) :
    (∑ h : ZMod k, ‖multiplicationPushforward h F j‖) ≤
      ∑ u : ZMod k, (u.val.gcd k : ℝ)*‖F u‖ := by
  classical
  calc
    _ ≤ ∑ h : ZMod k, ∑ u : ZMod k, if h*u=j then ‖F u‖ else 0 := by
      apply Finset.sum_le_sum
      intro h _
      exact (norm_sum_le _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp)
    _ = ∑ u : ZMod k,
        ((Finset.univ.filter (fun h : ZMod k => h*u=j)).card : ℝ)*‖F u‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast multiplication_fibre_card_le u j) (norm_nonneg _)

theorem sum_multiples_range {d q : ℕ} (hd : 0 < d) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.range (d*q), if d ∣ u then f u else 0) =
      ∑ r ∈ Finset.range q, f (d*r) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun r _ => d*r)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hr) hd, dvd_mul_right _ _⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro u hu
    obtain ⟨hul, hdu⟩ := Finset.mem_filter.mp hu
    refine ⟨u/d, Finset.mem_range.mpr ?_, Nat.mul_div_cancel' hdu⟩
    exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [mul_comm] using Finset.mem_range.mp hul)
  · intro r _
    rfl

theorem scaled_frequency_mass_bound {d : ℕ} (hd : d ∈ k.divisors) :
    (d : ℝ)*(∑ u : ZMod k, if d ∣ u.val then
      ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖ else 0) ≤
        (k : ℝ)*(harmonic k : ℝ)/2 := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdk := Nat.dvd_of_mem_divisors hd
  let q := k/d
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd (NeZero.pos k) hdk) hdpos
  have hk : k=d*q := (Nat.mul_div_cancel' hdk).symm
  have he : (∑ u : ZMod k, if d ∣ u.val then
      ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖ else 0) =
      ∑ r ∈ Finset.range q, ‖sawtoothFourier (d*q) (d*r)‖ := by
    simp_rw [norm_dft_centeredSawtooth_eq]
    rw [CommonResetBernoulliLifts.sum_residue_values
      (fun v => if d ∣ v then ‖sawtoothFourier k v‖ else 0),
      hk, sum_multiples_range hdpos]
  rw [he]
  calc
    _ ≤ (d : ℝ)*(∑ r ∈ Finset.range q, frequencyEnvelope q r) := by
      gcongr with r hr
      exact norm_scaled_sawtoothFourier_le_envelope hdpos hq (Finset.mem_range.mp hr)
    _ ≤ (d : ℝ)*((q : ℝ)*(harmonic q : ℝ)/2) := by
      gcongr
      exact frequencyEnvelope_sum_le hq
    _ ≤ (d : ℝ)*((q : ℝ)*(harmonic k : ℝ)/2) := by
      gcongr
      exact_mod_cast harmonic_cast_mono (Nat.div_le_self k d)
    _ = _ := by rw [hk]; push_cast; ring

theorem sawtooth_gcd_frequency_mass_bound :
    (∑ u : ZMod k, (u.val.gcd k : ℝ)*
      ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖) ≤
      (k.divisors.card : ℝ)*((k : ℝ)*(harmonic k : ℝ)/2) := by
  classical
  have hgcd (u : ZMod k) : (u.val.gcd k : ℝ) ≤
      ∑ d ∈ k.divisors, if d ∣ u.val then (d : ℝ) else 0 := by
    have hg : u.val.gcd k ∈ k.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, NeZero.ne k⟩
    have hl := Finset.single_le_sum
      (f := fun d => if d ∣ u.val then (d : ℝ) else 0)
      (fun d _ => by split_ifs <;> positivity) hg
    simpa only [Nat.gcd_dvd_left, ite_true] using hl
  calc
    _ ≤ ∑ u : ZMod k, (∑ d ∈ k.divisors,
        if d ∣ u.val then (d : ℝ) else 0)*
          ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖ := by
      exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (hgcd u) (norm_nonneg _))
    _ = ∑ d ∈ k.divisors, (d : ℝ)*
        (∑ u : ZMod k, if d ∣ u.val then
          ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖ else 0) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ ≤ ∑ _d ∈ k.divisors, (k : ℝ)*(harmonic k : ℝ)/2 :=
      Finset.sum_le_sum (fun d hd => scaled_frequency_mass_bound hd)
    _ = _ := by simp

def resetFourierMatrix (j h : ZMod k) : ℂ :=
  (2/(k : ℂ))*multiplicationPushforward h
    (ZMod.dft (centeredSawtooth : ZMod k → ℂ)) j

theorem resetFourierMatrix_norm (j h : ZMod k) :
    ‖resetFourierMatrix j h‖ = (2/(k : ℝ))*
      ‖multiplicationPushforward h (ZMod.dft (centeredSawtooth : ZMod k → ℂ)) j‖ := by
  simp [resetFourierMatrix]

theorem resetFourierMatrix_column_bound (h : ZMod k) :
    (∑ j : ZMod k, ‖resetFourierMatrix j h‖) ≤ (harmonic k : ℝ) := by
  simp_rw [resetFourierMatrix_norm]
  rw [← Finset.mul_sum]
  have hmass : (∑ j : ZMod k,
      ‖multiplicationPushforward h (ZMod.dft (centeredSawtooth : ZMod k → ℂ)) j‖) ≤
        (k : ℝ)*(harmonic k : ℝ)/2 := by
    calc
      _ ≤ ∑ u : ZMod k, ‖ZMod.dft (centeredSawtooth : ZMod k → ℂ) u‖ :=
        pushforward_mass_le h _
      _ ≤ _ := by
        rw [dft_centeredSawtooth_normMass_eq]
        exact sawtoothFourierNormMass_le (NeZero.pos k)
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  calc
    _ ≤ (2/(k : ℝ))*((k : ℝ)*(harmonic k : ℝ)/2) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by field_simp

theorem resetFourierMatrix_row_bound (j : ZMod k) :
    (∑ h : ZMod k, ‖resetFourierMatrix j h‖) ≤
      (k.divisors.card : ℝ)*(harmonic k : ℝ) := by
  simp_rw [resetFourierMatrix_norm]
  rw [← Finset.mul_sum]
  have hmass := (multiplication_pushforward_row_bound
    (ZMod.dft (centeredSawtooth : ZMod k → ℂ)) j).trans
      sawtooth_gcd_frequency_mass_bound
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  calc
    _ ≤ (2/(k : ℝ))*((k.divisors.card : ℝ)*((k : ℝ)*(harmonic k : ℝ)/2)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by field_simp

def completeGridField (c : ZMod k → ℂ) (x : ZMod k) : ℂ :=
  2*∑ h : ZMod k, c h*centeredSawtooth (h*x)

theorem dft_completeGridField (c : ZMod k → ℂ) (j : ZMod k) :
    ZMod.dft (completeGridField c) j =
      (k : ℂ)*(∑ h : ZMod k, resetFourierMatrix j h*c h) := by
  classical
  have hswap : ZMod.dft (completeGridField c) j =
      2*∑ h : ZMod k, c h*ZMod.dft (fun x => centeredSawtooth (h*x)) j := by
    simp only [ZMod.dft_apply, completeGridField, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hswap]
  simp_rw [dft_comp_mul]
  simp only [resetFourierMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  field_simp [NeZero.ne (k : ℂ)]

theorem complete_grid_energy_bound (c : ZMod k → ℂ) :
    (1/(k : ℝ))*(∑ x : ZMod k, ‖completeGridField c x‖^2) ≤
      (k.divisors.card : ℝ)*(harmonic k : ℝ)^2*
        (∑ h : ZMod k, ‖c h‖^2) := by
  have hH : (0 : ℝ) ≤ (harmonic k : ℝ) :=
    le_of_lt (by exact_mod_cast harmonic_pos (NeZero.ne k))
  have hs := finite_schur_bound Finset.univ Finset.univ resetFourierMatrix c
    (R := (k.divisors.card : ℝ)*(harmonic k : ℝ))
    (C := (harmonic k : ℝ)) (by positivity) hH
    (fun j _ => resetFourierMatrix_row_bound j)
    (fun h _ => resetFourierMatrix_column_bound h)
  have he : (∑ j : ZMod k, ‖ZMod.dft (completeGridField c) j‖^2) =
      (k : ℝ)^2*(∑ j : ZMod k,
        ‖∑ h : ZMod k, resetFourierMatrix j h*c h‖^2) := by
    simp_rw [dft_completeGridField, norm_mul, Complex.norm_natCast, mul_pow]
    rw [Finset.mul_sum]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have heq : (1/(k : ℝ))*(∑ x : ZMod k, ‖completeGridField c x‖^2) =
      ∑ j : ZMod k, ‖∑ h : ZMod k, resetFourierMatrix j h*c h‖^2 := by
    calc
      _ = (1/(k : ℝ)^2)*((k : ℝ)*(∑ x : ZMod k, ‖completeGridField c x‖^2)) := by
        field_simp
      _ = (1/(k : ℝ)^2)*(∑ j : ZMod k, ‖ZMod.dft (completeGridField c) j‖^2) := by
        rw [dft_parseval]
      _ = _ := by rw [he]; field_simp
  rw [heq]
  convert hs using 1
  ring

end NField.ResetForests.ResetGrid
