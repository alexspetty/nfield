/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RawClock
import NField.ResetForests.Centered
import NField.ResetForests.DivisorBudget
/-! # Complete centered phase cells

Both prime branches contribute their actual divisors. The complete clock
bound is summed over this full population before any small-power estimate.
-/

noncomputable section

namespace NField.ResetForests.PhasePopulations

open scoped BigOperators
open NField.Alignment
open CenteredPhase DedekindFourierMoment

def phaseClocks (p h : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p-1)).filter (fun k => centeredPhase p k=h)

def phaseWork (p h : ℕ) : ℝ :=
  ∑ k ∈ phaseClocks p h, |4*Core.clockReading (p-1) (p^2) k|

def phaseDivisorMaximum (p : ℕ) : ℕ :=
  (Finset.Icc 1 (2*p)).sup (fun n => n.divisors.card)

theorem divisor_count_le_phase_maximum {p n : ℕ} (hn : 0 < n) (hnp : n ≤ 2*p) :
    n.divisors.card ≤ phaseDivisorMaximum p := by
  exact Finset.le_sup (f := fun n => n.divisors.card) (Finset.mem_Icc.mpr ⟨hn, hnp⟩)

theorem phase_divisor_subset {p h : ℕ} (hp : p.Prime) :
    phaseClocks p h ⊆ (p-h).divisors ∪ (p+h).divisors := by
  intro k hk
  obtain ⟨hkI, he⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk2, hkpN⟩ := Finset.mem_Icc.mp hkI
  have hkp : k < p := by omega
  have hr := centered_phase_range hp hk2 hkp
  have hh : h < p := by
    rw [he] at hr
    exact hr.2.trans_lt (Nat.div_lt_self hp.pos (by decide : 1 < 3))
  by_cases hl : p%k ≤ k-p%k
  · have hd := (centered_lower_branch hp hk2 hkp hl).1
    rw [he] at hd
    exact Finset.mem_union_left _ (Nat.mem_divisors.mpr ⟨hd, by omega⟩)
  · have hd := (centered_upper_branch hp hk2 hkp (by omega)).1
    rw [he] at hd
    exact Finset.mem_union_right _ (Nat.mem_divisors.mpr ⟨hd, by omega⟩)

theorem phase_clock_card_bound {p h : ℕ} (hp : p.Prime) (hh : h < p) :
    (phaseClocks p h).card ≤ 2*phaseDivisorMaximum p := by
  have hA := divisor_count_le_phase_maximum (p := p) (n := p-h) (by omega) (by omega)
  have hB := divisor_count_le_phase_maximum (p := p) (n := p+h) (by have := hp.pos; omega) (by omega)
  calc
    _ ≤ ((p-h).divisors ∪ (p+h).divisors).card := Finset.card_le_card (phase_divisor_subset hp)
    _ ≤ (p-h).divisors.card+(p+h).divisors.card := Finset.card_union_le _ _
    _ ≤ _ := by omega

theorem divisor_sum_ratio_le_card {k : ℕ} (hk : 0 < k) :
    (divisorSumOne k : ℝ)/(k : ℝ) ≤ (k.divisors.card : ℝ) := by
  have hs : divisorSumOne k ≤ k.divisors.card*k := by
    unfold divisorSumOne
    calc
      _ ≤ ∑ _d ∈ k.divisors, k :=
        Finset.sum_le_sum (fun d hd => Nat.le_of_dvd hk (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp
  apply (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).mpr
  exact_mod_cast hs

theorem raw_clock_card_bound {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) :
    |4*Core.clockReading (p-1) (p^2) k| ≤
      2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(k.divisors.card : ℝ) := by
  calc
    _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ)/(k : ℝ) :=
      raw_clock_divisor_bound hp hk hkp
    _ = (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*((divisorSumOne k : ℝ)/(k : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisor_sum_ratio_le_card (by omega : 0 < k)) (by positivity)

theorem phase_work_finite_bound {p h : ℕ} (hp : p.Prime) :
    phaseWork p h ≤
      4*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ)^2 := by
  by_cases hh : h < p
  · calc
      _ ≤ ∑ _k ∈ phaseClocks p h,
          2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkI := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
        have hkp : k < p := by omega
        exact (raw_clock_card_bound hp hkI.1 hkp).trans
          (mul_le_mul_of_nonneg_left
            (by exact_mod_cast divisor_count_le_phase_maximum (p := p) (n := k) (by omega) (by omega))
            (by positivity))
      _ = ((phaseClocks p h).card : ℝ)*
          (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ)) := by simp
      _ ≤ (2*(phaseDivisorMaximum p : ℝ))*
          (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast phase_clock_card_bound hp hh) (by positivity)
      _ = _ := by ring
  · have hempty : phaseClocks p h=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hkI, he⟩ := Finset.mem_filter.mp hk
      obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hkI
      have hr := centered_phase_range hp hk2 (by omega : k < p)
      rw [he] at hr
      have hlt := Nat.div_lt_self hp.pos (by decide : 1 < 3)
      omega
    simp only [phaseWork, hempty, Finset.sum_empty]
    positivity

theorem phase_divisor_maximum_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p →
      (phaseDivisorMaximum p : ℝ) ≤ C*(p : ℝ)^ε := by
  obtain ⟨D, hD, hd⟩ := DivisorSmallPowerBound.divisor_count_small_power ε hε
  refine ⟨D*(2 : ℝ)^ε, by positivity, ?_⟩
  intro p hp
  have hne : (Finset.Icc 1 (2*p)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 (2*p)) hne
    (fun n : ℕ => n.divisors.card)
  have hnI := Finset.mem_Icc.mp hn
  change (((Finset.Icc 1 (2*p)).sup (fun n => n.divisors.card) : ℕ) : ℝ)≤_
  rw [he]
  calc
    _ ≤ D*(n : ℝ)^ε := hd n hnI.1
    _ ≤ D*(2*(p : ℝ))^ε := by
      gcongr
      exact_mod_cast hnI.2
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

theorem harmonic_small_power_from_mathlib (ε : ℝ) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) :
    (harmonic n : ℝ) ≤ (1+1/ε)*(n : ℝ)^ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.one_le_rpow hnR hε.le
  have hl := Real.log_natCast_le_rpow_div n hε
  have hh := harmonic_le_one_add_log n
  simp only [div_eq_mul_inv] at hl ⊢
  nlinarith

def phaseArithmeticCost (p : ℕ) : ℝ :=
  (harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ)^2

theorem phase_arithmetic_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p →
      phaseArithmeticCost p ≤ C*(p : ℝ)^ε := by
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D, hD, hd⟩ := phase_divisor_maximum_small_power δ hδ
  let H : ℝ := 1+1/δ
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H^2*D^2, by positivity, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hhn : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hh : (harmonic (p-1) : ℝ) ≤ H*(p : ℝ)^δ :=
    (harmonic_cast_mono (Nat.sub_le p 1)).trans (harmonic_small_power_from_mathlib δ hδ hp)
  calc
    phaseArithmeticCost p ≤ (H*(p : ℝ)^δ)^2*(D*(p : ℝ)^δ)^2 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hhn hh 2
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hd p hp) 2
      · positivity
      · positivity
    _ = (H^2*D^2)*(((p : ℝ)^δ)^2*((p : ℝ)^δ)^2) := by ring
    _ = (H^2*D^2)*(p : ℝ)^(δ*2+δ*2) := by
      rw [← Real.rpow_mul_natCast hpR.le, ← Real.rpow_add hpR]
      norm_num
    _ = _ := by
      congr 2
      dsimp [δ]
      ring

/-- A uniform explicit inequality implies the printed one-plus-epsilon cell bound. -/
theorem phase_work_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∀ h : ℕ,
      phaseWork p h ≤ C*(p : ℝ)^(1+ε) := by
  obtain ⟨C, hC, hc⟩ := phase_arithmetic_small_power ε hε
  refine ⟨4*C, by positivity, ?_⟩
  intro p hp h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    _ ≤ 4*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(phaseDivisorMaximum p : ℝ)^2 :=
      phase_work_finite_bound hp
    _ = 4*((p-1 : ℕ) : ℝ)*phaseArithmeticCost p := by unfold phaseArithmeticCost; ring
    _ ≤ 4*(p : ℝ)*(C*(p : ℝ)^ε) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le p 1) (by norm_num)
      · exact hc p hp.one_le
      · unfold phaseArithmeticCost
        positivity
      · positivity
    _ = _ := by rw [Real.rpow_add hpR, Real.rpow_one]; ring

end NField.ResetForests.PhasePopulations
