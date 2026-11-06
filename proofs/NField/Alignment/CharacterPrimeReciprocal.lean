/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CharacterMertensBounds
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!+# Ordinary convergence of nonprincipal prime reciprocal character sums

Dirichlet's test is applied to the proved bounded logarithmic character
sums. The prime-power correction is absolutely summable by Mathlib.
All prime sums below use ordered natural cutoffs.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CharacterPrimeReciprocal

open Filter Finset ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction
open NField.Alignment.CharacterMertensBounds
open NField.Alignment.MagnitudeLTruncation

variable {q : ℕ} [NeZero q]

def logWeightedMangoldt (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (Real.log n)⁻¹ • mangoldtCharacter χ n

def primeReciprocal (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then χ (n : ZMod q) / (n : ℂ) else 0

theorem shifted_mangoldt_partial_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ i ∈ Finset.range N, mangoldtCharacter χ (i + 2)‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := mangoldt_character_partial_bound χ hχ
  refine ⟨C, fun N => ?_⟩
  have h := hC (N + 1)
  have hset : Finset.Ioc 0 (N + 1) = Finset.Icc 1 (N + 1) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hset, positive_interval_sum_eq_range, Finset.sum_range_succ'] at h
  simpa [mangoldtCharacter, harmonicCharacter, Nat.add_assoc] using h

theorem logWeightedMangoldt_cauchy (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, logWeightedMangoldt χ n) := by
  obtain ⟨C, hC⟩ := shifted_mangoldt_partial_bound χ hχ
  have hanti : Antitone (fun n : ℕ => (Real.log (n + 2 : ℕ))⁻¹) := by
    intro m n hmn
    apply inv_anti₀
    · exact Real.log_pos (by exact_mod_cast (show 1 < m + 2 by omega))
    · apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 2
  have hlog : Tendsto (fun n : ℕ => Real.log (n + 2 : ℕ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hzero : Tendsto (fun n : ℕ => (Real.log (n + 2 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hC
  rw [← cauchySeq_shift 2]
  have heq (N : ℕ) :
      (∑ n ∈ Finset.range (N + 2), logWeightedMangoldt χ n) =
        ∑ n ∈ Finset.range N, (Real.log (n + 2 : ℕ))⁻¹ • mangoldtCharacter χ (n + 2) := by
    rw [show N + 2 = 2 + N by omega, Finset.sum_range_add]
    simp [logWeightedMangoldt, mangoldtCharacter, harmonicCharacter,
      Finset.sum_range_succ, Nat.add_comm]
  simpa only [heq] using h

theorem nonprime_mangoldt_summable :
    Summable (fun n : ℕ => (if n.Prime then (0 : ℝ) else Λ n) / (n : ℝ)) := by
  have hz (n : ℕ) : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simpa [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, hz] using
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)

theorem logWeightedMangoldt_norm_bound (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖logWeightedMangoldt χ n‖ ≤ (Real.log 2)⁻¹ * (Λ n / (n : ℝ)) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [logWeightedMangoldt, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlog.le)]
  apply mul_le_mul
  · apply inv_anti₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  · exact norm_mangoldtCharacter_le χ n
  · exact norm_nonneg _
  · positivity

theorem nonprime_logWeightedMangoldt_summable (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ => if n.Prime then (0 : ℂ) else logWeightedMangoldt χ n) := by
  apply (nonprime_mangoldt_summable.mul_left (Real.log 2)⁻¹).of_norm_bounded
  intro n
  by_cases hn : n.Prime
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    by_cases hlarge : 2 ≤ n
    · exact logWeightedMangoldt_norm_bound χ hlarge
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl <;>
        simp [logWeightedMangoldt, mangoldtCharacter, harmonicCharacter]

theorem logWeightedMangoldt_eq_primeReciprocal {χ : DirichletCharacter ℂ q}
    {n : ℕ} (hn : n.Prime) :
    logWeightedMangoldt χ n = primeReciprocal χ n := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
  simp only [logWeightedMangoldt, mangoldtCharacter, harmonicCharacter,
    ArithmeticFunction.coe_mk, Complex.real_smul, vonMangoldt_apply_prime hn,
    primeReciprocal, hn, ↓reduceIte, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlog), one_mul]

/-- Title: `Nonprincipal prime reciprocal convergence`.
The sum is over actual primes in increasing natural cutoffs. -/
theorem primeReciprocal_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ L : ℂ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, primeReciprocal χ n)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (logWeightedMangoldt_cauchy χ hχ)
  have htail := (nonprime_logWeightedMangoldt_summable χ).hasSum.tendsto_sum_nat
  refine ⟨L - ∑' n : ℕ, (if n.Prime then (0 : ℂ) else logWeightedMangoldt χ n), ?_⟩
  have h := hL.sub htail
  convert h using 1
  ext N
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · simp only [hn, ↓reduceIte, sub_zero, logWeightedMangoldt_eq_primeReciprocal hn]
  · simp [primeReciprocal, hn]

end NField.Alignment.CharacterPrimeReciprocal
