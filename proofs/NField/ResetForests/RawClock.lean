/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ClockBinary
import NField.ResetForests.Sampling
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
/-! # Complete-clock inversion and the literal divisor bound

Mathlib's finite Möbius inversion is applied to the exact partition of the
complete grid by reduced denominator. The original source and sampler stay
fixed through that inversion.
-/

noncomputable section

namespace NField.ResetForests.PhasePopulations

open scoped BigOperators
open NField.Alignment
open ClockRows CommonResetBernoulliLifts EndpointReciprocityBridge
open RademacherThreeTerm DedekindReciprocity DedekindFourierMoment

def fullClock (N Q d : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, Core.completeCorrelation Q j d

def primitiveClock (N Q d : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, (primitiveCoefficientCorrelation Q j d : ℝ)

def divisorSumOne (k : ℕ) : ℕ := ∑ d ∈ k.divisors, d

theorem full_clock_divisor_partition (N Q : ℕ) {d : ℕ} (hd : 0 < d) :
    fullClock N Q d = ∑ k ∈ d.divisors, primitiveClock N Q k := by
  unfold fullClock primitiveClock Core.completeCorrelation
  simp_rw [coefficient_swap, arithmeticCoefficientDedekindTerm_eq_primitiveDivisorSum hd,
    Rat.cast_sum]
  rw [Finset.sum_comm]

theorem primitive_clock_inversion (N Q : ℕ) {k : ℕ} (hk : 0 < k) :
    primitiveClock N Q k = ∑ d ∈ k.divisors,
      (ArithmeticFunction.moebius (k/d) : ℝ)*fullClock N Q d := by
  have hf : ∀ d : ℕ, 0 < d → (∑ e ∈ d.divisors, primitiveClock N Q e)=fullClock N Q d :=
    fun d hd => (full_clock_divisor_partition N Q hd).symm
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hf) k hk
  rw [Nat.sum_divisorsAntidiagonal'
    (fun x y => (ArithmeticFunction.moebius x : ℝ)*fullClock N Q y)] at hi
  exact hi.symm

theorem full_clock_one (N Q : ℕ) : fullClock N Q 1=0 := by
  simp [fullClock, Core.completeCorrelation, arithmeticCoefficientDedekindTerm,
    rationalSawtooth]

theorem full_clock_divisor_bound {p k d : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) (hd : d ∈ k.divisors) :
    |fullClock (p-1) (p^2) d| ≤ (d : ℝ)/4*(harmonic (p-1) : ℝ)^2 := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdk := Nat.le_of_dvd (by omega : 0 < k) (Nat.dvd_of_mem_divisors hd)
  by_cases hd1 : d=1
  · subst d
    rw [full_clock_one, abs_zero]
    positivity
  · have hd2 : 2 ≤ d := by omega
    have hs := whole_clock_work_bound hp hd2 (by omega : d < p)
    have hH : (0 : ℝ) ≤ (harmonic (d/2) : ℝ) := by
      simpa using harmonic_cast_mono (Nat.zero_le (d/2))
    have hmono : (harmonic (d/2) : ℝ) ≤ (harmonic (p-1) : ℝ) :=
      harmonic_cast_mono ((Nat.div_le_self d 2).trans (by omega))
    exact hs.trans (by gcongr)

theorem primitive_clock_bound {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) :
    |primitiveClock (p-1) (p^2) k| ≤
      (divisorSumOne k : ℝ)/4*(harmonic (p-1) : ℝ)^2 := by
  rw [primitive_clock_inversion _ _ (by omega : 0 < k)]
  calc
    _ ≤ ∑ d ∈ k.divisors,
        |(ArithmeticFunction.moebius (k/d) : ℝ)*fullClock (p-1) (p^2) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ k.divisors, (d : ℝ)/4*(harmonic (p-1) : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius (k/d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k/d))
      exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans
        (by simpa only [one_mul] using full_clock_divisor_bound hp hk hkp hd)
    _ = _ := by
      unfold divisorSumOne
      push_cast
      rw [← Finset.sum_mul, ← Finset.sum_div]

theorem clock_reading_primitive (N Q : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    Core.clockReading N Q k = 2*((N/k : ℕ) : ℝ)*primitiveClock N Q k := by
  unfold Core.clockReading primitiveClock
  rw [CommonResetDedekind.source_row hk]
  ring

/-- The finite inequality printed as equation 6.2, with its actual clock work. -/
theorem raw_clock_divisor_bound {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) :
    |4*Core.clockReading (p-1) (p^2) k| ≤
      2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ)/(k : ℝ) := by
  rw [clock_reading_primitive _ _ hk]
  have hm : (((p-1)/k : ℕ) : ℝ) ≤ ((p-1 : ℕ) : ℝ)/(k : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast (by omega : 0 < k))).mpr
    exact_mod_cast Nat.div_mul_le_self (p-1) k
  calc
    _ = 8*(((p-1)/k : ℕ) : ℝ)*|primitiveClock (p-1) (p^2) k| := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ 8*(((p-1)/k : ℕ) : ℝ)*
        ((divisorSumOne k : ℝ)/4*(harmonic (p-1) : ℝ)^2) := by
      exact mul_le_mul_of_nonneg_left (primitive_clock_bound hp hk hkp) (by positivity)
    _ = 2*(((p-1)/k : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ) := by ring
    _ ≤ 2*(((p-1 : ℕ) : ℝ)/(k : ℝ))*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ) := by
      gcongr
    _ = _ := by ring

end NField.ResetForests.PhasePopulations
