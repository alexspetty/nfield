/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeLTruncation
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!+# Bounded logarithmic character sums for progression Mertens limits

The endpoint is Mathlib's continued L-function, identified with ordered
partial sums by the existing character truncation theorem. Finite Dirichlet
convolution and the elementary Chebyshev bound supply the cancellation.+-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CharacterMertensBounds

open Filter Finset ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction
open NField.Alignment.MagnitudeLTruncation
open NField.Alignment.CollisionPeriodicLValue
open NField.Alignment.CollisionDirichletBoundary

variable {q : ℕ} [NeZero q]

def harmonicCharacter (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => χ (n : ZMod q) / (n : ℂ), by simp⟩

def mangoldtCharacter (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => (Λ n : ℂ) * harmonicCharacter χ n, by simp [harmonicCharacter]⟩

theorem harmonicCharacter_mul (χ : DirichletCharacter ℂ q) (m n : ℕ) :
    harmonicCharacter χ (m * n) = harmonicCharacter χ m * harmonicCharacter χ n := by
  simp only [harmonicCharacter, ArithmeticFunction.coe_mk, Nat.cast_mul, map_mul,
    div_mul_div_comm]

theorem mangoldtCharacter_convolution (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (mangoldtCharacter χ * harmonicCharacter χ) n =
      (Real.log n : ℂ) * harmonicCharacter χ n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m => mangoldtCharacter χ d * harmonicCharacter χ m)]
  calc
    (∑ d ∈ n.divisors, mangoldtCharacter χ d * harmonicCharacter χ (n / d)) =
        ∑ d ∈ n.divisors, (Λ d : ℂ) * harmonicCharacter χ n := by
      apply Finset.sum_congr rfl
      intro d hd
      change (Λ d : ℂ) * harmonicCharacter χ d * harmonicCharacter χ (n / d) = _
      rw [mul_assoc, ← harmonicCharacter_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = (Real.log n : ℂ) * harmonicCharacter χ n := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]

theorem harmonicCharacter_partial (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, harmonicCharacter χ n) = orderedLPartial χ N := by
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset, positive_interval_sum_eq_range]
  rfl

theorem character_log_convolution_sum (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n) =
      ∑ d ∈ Finset.Ioc 0 N, mangoldtCharacter χ d * orderedLPartial χ (N / d) := by
  simp_rw [← mangoldtCharacter_convolution]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  simp_rw [harmonicCharacter_partial]

theorem character_log_tail_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) :
    ‖∑ i ∈ Finset.range N,
      (Real.log (i + 3 : ℕ) / (i + 3 : ℕ) : ℝ) • χ ((i + 3 : ℕ) : ZMod q)‖ ≤
      (q : ℝ) * (Real.log 3 / 3) := by
  have hf0 (i : ℕ) : 0 ≤ Real.log (i + 3 : ℕ) / (i + 3 : ℕ) := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ i + 3 by omega)
    · positivity
  have hanti : Antitone (fun i : ℕ => Real.log (i + 3 : ℕ) / (i + 3 : ℕ)) := by
    intro i j hij
    apply Real.log_div_self_antitoneOn
    · change Real.exp 1 ≤ _
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ i + 3 by omega))
    · change Real.exp 1 ≤ _
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ j + 3 by omega))
    · exact_mod_cast Nat.add_le_add_right hij 3
  have h := norm_sum_range_smul_le hf0 hanti
    (fun n => shifted_character_sum_bound χ hχ 2 n) N
  simpa only [Nat.zero_add, Nat.cast_ofNat,
    show ∀ i : ℕ, 2 + i + 1 = i + 3 by omega] using h

theorem character_log_partial_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n‖ ≤ C := by
  let f : ℕ → ℂ := fun i =>
    (Real.log (i + 1 : ℕ) / (i + 1 : ℕ) : ℝ) • χ ((i + 1 : ℕ) : ZMod q)
  let C : ℝ := ‖∑ i ∈ Finset.range 2, f i‖ + (q : ℝ) * (Real.log 3 / 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun N => ?_⟩
  have heq : (∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n) =
      ∑ i ∈ Finset.range N, f i := by
    have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hset, positive_interval_sum_eq_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [f, harmonicCharacter, ArithmeticFunction.coe_mk, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [heq]
  by_cases hN : 2 ≤ N
  · rw [show N = 2 + (N - 2) by omega, Finset.sum_range_add]
    calc
      _ ≤ ‖∑ i ∈ Finset.range 2, f i‖ + ‖∑ i ∈ Finset.range (N - 2), f (2 + i)‖ :=
        norm_add_le _ _
      _ ≤ C := by
        dsimp [C]
        apply add_le_add_right
        simpa only [f, show ∀ i : ℕ, 2 + i + 1 = i + 3 by omega] using
          character_log_tail_bound χ hχ (N - 2)
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl <;> simpa [f] using hC

theorem norm_mangoldtCharacter_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖mangoldtCharacter χ n‖ ≤ Λ n / (n : ℝ) := by
  change ‖(Λ n : ℂ) * (χ (n : ZMod q) / (n : ℂ))‖ ≤ _
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Complex.norm_natCast]
  calc
    _ ≤ Λ n * (1 / (n : ℝ)) := by
      gcongr
      exact χ.norm_le_one _
    _ = _ := by ring

theorem div_floor_tail_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    (1 : ℝ) / d * (q : ℝ) / ((N / d : ℕ) + 1) ≤ (q : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : N < d * (N / d + 1) := by
    have hmod := Nat.mod_lt N hd
    have heq := Nat.mod_add_div N d
    nlinarith
  have hfloorR : (N : ℝ) ≤ (d : ℝ) * ((N / d : ℕ) + 1) := by
    exact_mod_cast hfloor.le
  calc
    _ = (q : ℝ) / ((d : ℝ) * ((N / d : ℕ) + 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (q : ℝ) / N := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hNR hfloorR

theorem mangoldt_convolution_error_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) :
    ‖(∑ d ∈ Finset.Ioc 0 N, mangoldtCharacter χ d) * DirichletCharacter.LFunction χ 1 -
      ∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n‖ ≤
      (q : ℝ) * (Real.log 4 + 4) := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.Ioc_self, Finset.sum_empty, zero_mul, sub_zero, norm_zero]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [character_log_convolution_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ d ∈ Finset.Ioc 0 N, mangoldtCharacter χ d *
        (DirichletCharacter.LFunction χ 1 - orderedLPartial χ (N / d))‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, ‖mangoldtCharacter χ d *
        (DirichletCharacter.LFunction χ 1 - orderedLPartial χ (N / d))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d * ((q : ℝ) / N) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      rw [norm_mul]
      calc
        _ ≤ (Λ d / (d : ℝ)) * ((q : ℝ) / ((N / d : ℕ) + 1)) :=
          mul_le_mul (norm_mangoldtCharacter_le χ d) (l_one_tail_bound_succ χ hχ _)
            (norm_nonneg _) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
        _ = Λ d * ((1 : ℝ) / d * (q : ℝ) / ((N / d : ℕ) + 1)) := by ring
        _ ≤ Λ d * ((q : ℝ) / N) :=
          mul_le_mul_of_nonneg_left (div_floor_tail_bound hNpos hdpos) vonMangoldt_nonneg
    _ = Chebyshev.psi N * ((q : ℝ) / N) := by
      rw [← Finset.sum_mul]
      simp only [Chebyshev.psi, Nat.floor_natCast]
    _ ≤ (Real.log 4 + 4) * N * ((q : ℝ) / N) :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))
        (by positivity)
    _ = (q : ℝ) * (Real.log 4 + 4) := by
      field_simp

/-- Cancellation in the actual nonprincipal logarithmic character sum.
The only hypothesis is that the character is nonprincipal. -/
theorem mangoldt_character_partial_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.Ioc 0 N, mangoldtCharacter χ n‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := character_log_partial_bound χ hχ
  have hL : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  refine ⟨((q : ℝ) * (Real.log 4 + 4) + C) / ‖DirichletCharacter.LFunction χ 1‖,
    by positivity, fun N => ?_⟩
  apply (le_div_iff₀ hL).mpr
  rw [← norm_mul]
  calc
    _ ≤ ‖(∑ n ∈ Finset.Ioc 0 N, mangoldtCharacter χ n) * DirichletCharacter.LFunction χ 1 -
          ∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n‖ +
          ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n‖ :=
      by
        have h := norm_add_le
          ((∑ n ∈ Finset.Ioc 0 N, mangoldtCharacter χ n) * DirichletCharacter.LFunction χ 1 -
            ∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n)
          (∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * harmonicCharacter χ n)
        simpa only [sub_add_cancel] using h
    _ ≤ _ := add_le_add (mangoldt_convolution_error_bound χ hχ N) (hbound N)

end NField.Alignment.CharacterMertensBounds
