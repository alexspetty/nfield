/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetLinearTailAssembly
import NField.Alignment.DivisorSmallPowerBound

/-! # Uniform small-power growth of the literal tail cost -/

noncomputable section

namespace NField.Alignment.CommonResetTailGrowth

open scoped BigOperators
open CommonResetDivisorFibers CommonResetSmallConductors CommonResetLinearTailAssembly

theorem harmonic_small_power (ε : ℝ) (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (harmonic n : ℝ) ≤ (1+1/ε)*(n : ℝ)^ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.one_le_rpow hnR hε.le
  have hl := Real.log_natCast_le_rpow_div n hε
  have hh := harmonic_le_one_add_log n
  simp only [div_eq_mul_inv] at hl ⊢
  nlinarith

theorem divisorMaximum_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p →
      (divisorMaximum p : ℝ) ≤ C*(p : ℝ)^ε := by
  obtain ⟨D, hD, hd⟩ := DivisorSmallPowerBound.divisor_count_small_power (ε/3) (by positivity)
  refine ⟨D*(2 : ℝ)^(ε/3), by positivity, ?_⟩
  intro p hp
  have hne : (Finset.Icc 1 (2*p^3)).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    have hh : 1 ≤ p^3 := one_le_pow₀ hp
    omega
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 (2*p^3)) hne
    (fun n : ℕ => n.divisors.card)
  have hnD := Finset.mem_Icc.mp hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  change (((Finset.Icc 1 (2*p^3)).sup (fun n : ℕ => n.divisors.card) : ℕ) : ℝ) ≤ _
  rw [he]
  calc
    _ ≤ D*(n : ℝ)^(ε/3) := hd n hnD.1
    _ ≤ D*(2*(p : ℝ)^3)^(ε/3) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
      exact_mod_cast hnD.2
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hpR.le]
      norm_num only [Nat.cast_ofNat]
      have heps : (3 : ℝ)*(ε/3) = ε := by ring
      rw [heps]
      ring

def tailArithmeticCost (p : ℕ) : ℝ := (divisorMaximum p : ℝ)*(harmonic p : ℝ)^4

/-- Title: `The actual divisor maximum and four harmonic factors cost any positive power`. -/
theorem tail_arithmetic_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p → tailArithmeticCost p ≤ C*(p : ℝ)^ε := by
  obtain ⟨D, hD, hd⟩ := divisorMaximum_small_power (ε/2) (by positivity)
  let H : ℝ := 1+1/(ε/8)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨D*H^4, by positivity, ?_⟩
  intro p hp
  have hdiv := hd p hp
  have hh := harmonic_small_power (ε/8) (by positivity) hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  calc
    tailArithmeticCost p ≤ (D*(p : ℝ)^(ε/2))*(H*(p : ℝ)^(ε/8))^4 := by
      apply mul_le_mul hdiv
      · exact pow_le_pow_left₀ (harmonic_nonneg _) hh 4
      · exact pow_nonneg (harmonic_nonneg _) _
      · positivity
    _ = (D*H^4)*((p : ℝ)^(ε/2)*((p : ℝ)^(ε/8))^4) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hpR.le, ← Real.rpow_add hpR]
      congr 2
      ring

/-- Title: `The complete linear-frequency tail has the published two-plus-epsilon bound`. -/
theorem linear_frequency_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∀ U J V : ℕ,
      U < p → J < p → 0 < V → ∀ (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ),
      (∀ u ∈ Finset.Icc 1 U, ∀ j ∈ Finset.Icc 1 J, ∀ t ∈ S u j,
        2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*j < t ∧ u.Coprime t) →
      |selectedLinearTail p U J (V+1) S length| ≤ C*(p : ℝ)^(2+ε)/(V : ℝ) := by
  obtain ⟨C, hC, hc⟩ := tail_arithmetic_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp U J V hU hJ hV S length hS
  have htail := linear_frequency_tail_finite_bound hp U J V hU hJ hV S length hS
  have hcost := hc p hp.one_le
  calc
    _ ≤ (p : ℝ)^2*tailArithmeticCost p/(V : ℝ) := by
      simpa only [tailArithmeticCost, mul_assoc] using htail
    _ ≤ (p : ℝ)^2*(C*(p : ℝ)^ε)/(V : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg V)
      exact mul_le_mul_of_nonneg_left hcost (sq_nonneg _)
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast hp.pos : (0 : ℝ) < p), Real.rpow_two]
      ring

end NField.Alignment.CommonResetTailGrowth
