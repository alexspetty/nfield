/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-! # The exact density of reflected targets among the positive even integers -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReflectedTargetDensity
open Filter
open scoped Topology

def targetCount (m T : ℕ) : ℕ :=
  ((Finset.Ioc 0 T).filter fun k => m ∣ 2 * k).card

theorem odd_modulus_count {m : ℕ} (hm : m.Coprime 2) (T : ℕ) :
    targetCount m T = T / m := by
  simp only [targetCount, hm.dvd_mul_left]
  exact Nat.Ioc_filter_dvd_card_eq_div T m

theorem base_ten_count (T : ℕ) : targetCount (10 ^ 2) T = T / 50 := by
  have h (k : ℕ) : 10 ^ 2 ∣ 2 * k ↔ 50 ∣ k := by omega
  simp only [targetCount, h]
  exact Nat.Ioc_filter_dvd_card_eq_div T 50

theorem quotient_density (m : ℕ) :
    Tendsto (fun T : ℕ => (T / m : ℕ) / (T : ℝ)) atTop (𝓝 ((m : ℝ)⁻¹)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (m : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg m))).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, mul_comm (m : ℝ)⁻¹, ← div_eq_mul_inv,
    Nat.floor_div_eq_div] using h

theorem odd_prime_density {b : ℕ} (hb : b.Prime) (hbodd : b ≠ 2) :
    Tendsto (fun T : ℕ => (targetCount (b ^ 2) T : ℝ) / T) atTop
      (𝓝 (((b : ℝ) ^ 2)⁻¹)) := by
  have hcop : (b ^ 2).Coprime 2 :=
    (hb.coprime_iff_not_dvd.mpr (fun h => hbodd ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hb.ne_one))).pow_left 2
  simp_rw [odd_modulus_count hcop]
  convert quotient_density (b ^ 2) using 1
  norm_cast

theorem base_ten_density :
    Tendsto (fun T : ℕ => (targetCount (10 ^ 2) T : ℝ) / T) atTop (𝓝 (1 / 50 : ℝ)) := by
  simp_rw [base_ten_count]
  simpa using quotient_density 50

end NField.Alignment.ReflectedTargetDensity
