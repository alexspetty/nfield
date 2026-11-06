/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalResolutionCurrent
import NField.Alignment.CollisionAmplitudeArithmetic

/-!
# Unprimitive rows and normalized resolution increments

These are the literal finite transforms used by the signed-current theorem.
The divisor inverse is proved through Mathlib's Möbius inversion.
-/

noncomputable section

namespace NField.Alignment.FiniteResolutionMass

open scoped BigOperators ArithmeticFunction
open FiniteResolutionCurrent ReciprocalResolutionCurrent

def unprimitiveRow (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ n.divisors, v k / (((n / k : ℕ) : ℝ) ^ 3)

def rowPotential (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * unprimitiveRow v n

def resolutionIncrement (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  rowPotential v (n + 1) - rowPotential v n

def normalizedSequence (v : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else resolutionIncrement v n / (4 * v 2), by simp⟩

@[simp] theorem unprimitive_row_zero (v : ℕ → ℝ) : unprimitiveRow v 0 = 0 := by
  simp [unprimitiveRow]

@[simp] theorem unprimitive_row_one (v : ℕ → ℝ) : unprimitiveRow v 1 = v 1 := by
  simp [unprimitiveRow]

/-- Title: `The unprimitive row is the cubic divisor lift of the mass`. -/
theorem unprimitive_row_literal (v : ℕ → ℝ) (n : ℕ) :
    unprimitiveRow v n = ∑ d ∈ n.divisors, v (n / d) / (d : ℝ) ^ 3 := by
  unfold unprimitiveRow
  rw [← Nat.sum_divisorsAntidiagonal (fun k d => v k / (d : ℝ) ^ 3),
    Nat.sum_divisorsAntidiagonal' (fun k d => v k / (d : ℝ) ^ 3)]

theorem unprimitive_row_weighted_divisors (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 * unprimitiveRow v n =
      ∑ k ∈ n.divisors, (k : ℝ) ^ 3 * v k := by
  unfold unprimitiveRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hk) hk0]
  field_simp

/-- Title: `Finite divisor inversion recovers the mass from its unprimitive rows`.

 The cubic divisor lift is inverted without any convergence assumption. -/
theorem mass_from_unprimitive_row (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    v n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 3 * unprimitiveRow v (n / d) := by
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun k => (k : ℝ) ^ 3 * v k)
    (g := fun k => (k : ℝ) ^ 3 * unprimitiveRow v k)).mp
      (fun k hk => (unprimitive_row_weighted_divisors v hk).symm) n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun d k => (ArithmeticFunction.moebius d : ℝ) *
      ((k : ℝ) ^ 3 * unprimitiveRow v k))] at hi
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 3 hn0))
  rw [← hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

/-- Title: `The unprimitive rows determine every mass`. -/
theorem unprimitive_rows_determine_mass (v u : ℕ → ℝ)
    (hrow : ∀ n, unprimitiveRow v n = unprimitiveRow u n)
    {n : ℕ} (hn : 0 < n) : v n = u n := by
  rw [mass_from_unprimitive_row v hn, mass_from_unprimitive_row u hn]
  simp only [hrow]

@[simp] theorem row_potential_zero (v : ℕ → ℝ) : rowPotential v 0 = 0 := by
  simp [rowPotential]

@[simp] theorem row_potential_one (v : ℕ → ℝ) : rowPotential v 1 = v 1 := by
  simp [rowPotential]

/-- Title: `The first resolution increment is four times the second mass`. -/
theorem first_resolution_increment (v : ℕ → ℝ) (hv1 : v 1 = 0) :
    resolutionIncrement v 1 = 4 * v 2 := by
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  norm_num [resolutionIncrement, rowPotential, unprimitiveRow, hd, hv1]

theorem normalized_sequence_one (v : ℕ → ℝ) (hv1 : v 1 = 0) (hv2 : v 2 ≠ 0) :
    normalizedSequence v 1 = 1 := by
  simp [normalizedSequence, first_resolution_increment v hv1, hv2]

/-- Title: `Normalized increments divide by four times the second mass`. -/
theorem normalized_sequence_apply (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    normalizedSequence v n = resolutionIncrement v n / (4 * v 2) := by
  simp [normalizedSequence, hn.ne']

def massCurrent (v : ℕ → ℝ) (hv1 : v 1 = 0) (hv2 : v 2 ≠ 0) (n : ℕ) : ℝ :=
  signedCurrent (normalizedSequence v) (normalized_sequence_one v hv1 hv2) n

theorem normalized_sequences_determine_increments (v u : ℕ → ℝ)
    (hv2 : v 2 ≠ 0) (hu2 : u 2 ≠ 0)
    (hseq : normalizedSequence v = normalizedSequence u) {n : ℕ} (hn : 0 < n) :
    resolutionIncrement v n = (v 2 / u 2) * resolutionIncrement u n := by
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) hseq
  rw [normalized_sequence_apply v hn, normalized_sequence_apply u hn] at h
  have hv : 4 * v 2 ≠ 0 := mul_ne_zero (by norm_num) hv2
  have hu : 4 * u 2 ≠ 0 := mul_ne_zero (by norm_num) hu2
  have he := (div_eq_div_iff hv hu).mp h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hu2).2
  nlinarith

theorem normalized_sequences_determine_rows (v u : ℕ → ℝ)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (hv2 : v 2 ≠ 0) (hu2 : u 2 ≠ 0)
    (hseq : normalizedSequence v = normalizedSequence u) (n : ℕ) :
    rowPotential v n = (v 2 / u 2) * rowPotential u n := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · simp [hn, hv1, hu1]
      have he := normalized_sequences_determine_increments v u hv2 hu2 hseq
        (Nat.pos_of_ne_zero hn)
      unfold resolutionIncrement at he
      nlinarith

theorem normalized_sequences_determine_unprimitive_rows (v u : ℕ → ℝ)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (hv2 : v 2 ≠ 0) (hu2 : u 2 ≠ 0)
    (hseq : normalizedSequence v = normalizedSequence u) (n : ℕ) :
    unprimitiveRow v n = (v 2 / u 2) * unprimitiveRow u n := by
  by_cases hn : n = 0
  · simp [hn]
  have h := normalized_sequences_determine_rows v u hv1 hu1 hv2 hu2 hseq n
  unfold rowPotential at h
  have hnR : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hn)
  apply mul_left_cancel₀ hnR
  nlinarith

/-- Title: `Normalized increments determine the mass up to its second-mass scale`. -/
theorem normalized_sequences_determine_mass_up_to_scale (v u : ℕ → ℝ)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (hv2 : v 2 ≠ 0) (hu2 : u 2 ≠ 0)
    (hseq : normalizedSequence v = normalizedSequence u) (n : ℕ) :
    v n = (v 2 / u 2) * u n := by
  by_cases hn : n = 0
  · simp [hn, hv0, hu0]
  have hnpos := Nat.pos_of_ne_zero hn
  rw [mass_from_unprimitive_row v hnpos, mass_from_unprimitive_row u hnpos,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [normalized_sequences_determine_unprimitive_rows v u hv1 hu1 hv2 hu2 hseq]
  ring

/-- Title: `Unit total mass makes the signed current injective`.

 Unit mass fixes the single scale left by normalized current reconstruction. -/
theorem mass_current_injective (v u : ℕ → ℝ)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (hv2 : v 2 ≠ 0) (hu2 : u 2 ≠ 0)
    (hvMass : ∑' k, v k = 1) (huMass : ∑' k, u k = 1)
    (hc : ∀ n, massCurrent v hv1 hv2 n = massCurrent u hu1 hu2 n) : v = u := by
  have hseq := signed_current_injective (normalizedSequence v) (normalizedSequence u)
    (normalized_sequence_one v hv1 hv2) (normalized_sequence_one u hu1 hu2) hc
  have hm := normalized_sequences_determine_mass_up_to_scale v u hv0 hu0 hv1 hu1
    hv2 hu2 hseq
  have hscale : v 2 / u 2 = 1 := by
    rw [tsum_congr hm, tsum_mul_left, huMass, mul_one] at hvMass
    exact hvMass
  funext n
  rw [hm n, hscale, one_mul]

end NField.Alignment.FiniteResolutionMass
