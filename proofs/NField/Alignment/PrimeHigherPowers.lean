/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeEulerLog
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Absolute and locally uniform convergence of the literal higher powers -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PrimeHigherPowers

open scoped BigOperators Topology
open NField.Alignment.PrimeEulerLog

def higherTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (pk : Nat.Primes × ℕ) : ℂ :=
  primeTerm χ s pk.1 ^ (pk.2 + 2) / (pk.2 + 2)

def majorant (σ : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  (pk.1 : ℝ) ^ (-2 * σ) * ((2 : ℝ) ^ (-σ)) ^ pk.2

theorem higherTerm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re)
    (pk : Nat.Primes × ℕ) : ‖higherTerm χ s pk‖ ≤ majorant σ pk := by
  rcases pk with ⟨p, k⟩
  have hp := primeTerm_norm_le_strip χ hs p
  have htwo := primeTerm_norm_le_two χ hσ hs p
  have hk : (1 : ℝ) ≤ k + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hsq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
    congr 1
    norm_num
    ring
  change ‖primeTerm χ s p ^ (k + 2) / (k + 2)‖ ≤ _
  rw [norm_div, norm_pow]
  have hden : ‖((k : ℂ) + 2)‖ = (k : ℝ) + 2 := by
    exact_mod_cast Complex.norm_natCast (k + 2)
  rw [hden]
  calc
    ‖primeTerm χ s p‖ ^ (k + 2) / ((k : ℝ) + 2) ≤
        ‖primeTerm χ s p‖ ^ (k + 2) := div_le_self (by positivity) hk
    _ = ‖primeTerm χ s p‖ ^ 2 * ‖primeTerm χ s p‖ ^ k := by
      rw [pow_add, mul_comm]
    _ ≤ ((p : ℝ) ^ (-σ)) ^ 2 * ((2 : ℝ) ^ (-σ)) ^ k := by gcongr
    _ = _ := by rw [hsq]; rfl

theorem majorant_summable {σ : ℝ} (hσ : 1 / 2 < σ) : Summable (majorant σ) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 * σ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hρ0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hρ : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact hp.mul_of_nonneg (summable_geometric_of_lt_one hρ0 hρ)
    (fun _ => by positivity) (fun _ => by positivity)

/-- Title: `The full double series of higher prime powers is absolutely convergent`. -/
theorem higherTerm_norm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ => ‖higherTerm χ s pk‖) := by
  exact (majorant_summable hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (higherTerm_norm_le χ (by linarith) le_rfl)

theorem higherTerm_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 / 2 < s.re) : HasSum (higherTerm χ s) (higherPowerSum χ s) := by
  have h := (higherTerm_norm_summable χ hs).of_norm
  have heq : (∑' pk : Nat.Primes × ℕ, higherTerm χ s pk) = higherPowerSum χ s := by
    rw [h.tsum_prod]
    exact tsum_congr fun p => (higherFactor_taylor χ (by linarith) p).tsum_eq
  exact heq ▸ h.hasSum

/-- Title: `Higher prime powers converge uniformly on each smaller right half-plane`. -/
theorem higherTerm_tendstoUniformlyOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    TendstoUniformlyOn
      (fun t : Finset (Nat.Primes × ℕ) => fun s : ℂ => ∑ pk ∈ t, higherTerm χ s pk)
      (higherPowerSum χ) Filter.atTop {s : ℂ | σ ≤ s.re} := by
  have h := tendstoUniformlyOn_tsum (majorant_summable hσ)
    (fun pk (s : ℂ) (hs : σ ≤ s.re) => higherTerm_norm_le χ (by linarith) hs pk)
  apply h.congr_right
  intro s hs
  exact (higherTerm_hasSum χ (hσ.trans_le hs)).tsum_eq

theorem higherTerm_literal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (pk : Nat.Primes × ℕ) :
    higherTerm χ s pk = χ pk.1 ^ (pk.2 + 2) /
      (((pk.2 + 2 : ℕ) : ℂ) * (pk.1 : ℂ) ^ (((pk.2 + 2 : ℕ) : ℂ) * s)) := by
  simpa only [higherTerm, Nat.cast_add, Nat.cast_ofNat] using
    primeTerm_pow_div χ s pk.1 (pk.2 + 2)

end NField.Alignment.PrimeHigherPowers
