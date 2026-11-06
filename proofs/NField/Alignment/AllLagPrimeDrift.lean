/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConstructiveFluctuationPrimeIdentity
import NField.Alignment.PrimeResidualCutoffs

/-! # The unconditional prime drift of the actual all-lag constructive fluctuation -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.CollisionTransformStrip

theorem allLagModulus_gt_base_add_one {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    b + 1 < allLagModulus b ell := by
  have hpow : b ^ 2 ≤ b ^ (ell + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hs : b + 1 < b ^ 2 := by nlinarith [sq_nonneg (b - 2 : ℤ)]
  exact hs.trans_le hpow

theorem constructive_prime_summand_eq {b ell p : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (hp : p.Prime) (hqp : allLagModulus b ell < p) :
    (constructiveFluctuation b ell p : ℂ) / (p : ℂ) =
      unitExtension (allLagUnitTable b ell) p / (p : ℂ) -
        unitExtension (remainderClassSignal b) p / (p : ℂ) - (correctionTail b p : ℂ) := by
  have hbp : b + 1 < p := (allLagModulus_gt_base_add_one hb hell).trans hqp
  have huq := prime_unit_of_modulus_lt hp hqp
  have hub := prime_unit_of_modulus_lt (q := b) hp (by omega)
  have hcop : (p % b).Coprime b := (ZMod.coprime_mod_iff_coprime p b).mpr
    ((ZMod.isUnit_iff_coprime p b).mp hub)
  have hmodpos : 1 ≤ p % b := by
    by_contra h
    have hz : p % b = 0 := by omega
    rw [hz] at hcop
    simp only [Nat.coprime_zero_left] at hcop
    omega
  have hR : (((p - 1) % b : ℕ) : ℂ) = ((p % b : ℕ) : ℂ) - 1 := by
    rw [pred_mod_eq_unit_remainder hb hub, Nat.cast_sub hmodpos]
    norm_num
  have hraw : unitExtension (allLagUnitTable b ell) p = (directAllLagDeviation b ell p : ℂ) := by
    rw [unitExtension, dif_pos huq, unit_table_eq_direct_deviation hb hell huq]
  have hc := congrArg (fun z : ℝ => (z : ℂ)) (constructiveFluctuation_div_identity (ell := ell) hb hbp)
  push_cast at hc
  rw [hR] at hc
  rw [hraw, unitExtension_remainder_eq hub]
  convert hc using 1 <;> ring

theorem raw_collision_tail_residual_limit {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell) (c : ℕ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc c ⌊x⌋₊,
        if p.Prime then unitExtension (allLagUnitTable b ell) p / (p : ℂ) else 0) -
          (-1 / 2 : ℂ) * (Real.log (Real.log x) : ℂ)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := periodic_prime_reciprocal_residual_limit (allLagUnitTable b ell)
  have hm := allLagUnitTable_grand_mean hb hell
  rw [ZMod.card_units_eq_totient] at hm
  rw [hm] at hL
  exact ⟨_, sum_Ioc_residual_cutoff_limit _ c _ hL⟩

theorem remainder_tail_residual_limit {b : ℕ} [NeZero b] (hb : 2 ≤ b) (c : ℕ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc c ⌊x⌋₊,
        if p.Prime then unitExtension (remainderClassSignal b) p / (p : ℂ) else 0) -
          (1 / 2 - 1 / (b : ℂ)) * (Real.log (Real.log x) : ℂ)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := remainder_prime_reciprocal_drift hb
  exact ⟨_, sum_Ioc_residual_cutoff_limit _ c _ hL⟩

theorem correction_tail_limit {b : ℕ} (hb : 2 ≤ b) (c : ℕ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc c ⌊x⌋₊, if p.Prime then (correctionTail b p : ℂ) else 0)
      atTop (𝓝 L) := by
  have hs : Summable (fun p : ℕ => if p.Prime then (correctionTail b p : ℂ) else 0) := by
    have h := Complex.summable_ofReal.mpr (correctionTail_prime_summable hb)
    apply h.congr
    intro p
    split_ifs <;> simp
  exact summable_Ioc_real_cutoff_limit _ hs (by simp [Nat.not_prime_zero]) c

/-- Title: `The actual all lag prime fluctuation has the universal drift`. -/
theorem all_lag_constructive_prime_drift
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ κ : ℝ, Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => constructiveFluctuation b ell p / (p : ℝ))
        (allLagModulus b ell) x +
          (((b : ℝ) - 1) / b) * Real.log (Real.log x)) atTop (𝓝 κ) := by
  let q := allLagModulus b ell
  obtain ⟨LS, hS⟩ := raw_collision_tail_residual_limit hb hell q
  obtain ⟨LR, hR⟩ := remainder_tail_residual_limit hb q
  obtain ⟨LE, hE⟩ := correction_tail_limit hb q
  have h := (hS.sub hR).sub hE
  have heq (x : ℝ) :
      ((realPrimeTailSum (fun p => constructiveFluctuation b ell p / (p : ℝ)) q x +
        (((b : ℝ) - 1) / b) * Real.log (Real.log x) : ℝ) : ℂ) =
      (((∑ p ∈ Finset.Ioc q ⌊x⌋₊,
        if p.Prime then unitExtension (allLagUnitTable b ell) p / (p : ℂ) else 0) -
          (-1 / 2 : ℂ) * (Real.log (Real.log x) : ℂ)) -
      ((∑ p ∈ Finset.Ioc q ⌊x⌋₊,
        if p.Prime then unitExtension (remainderClassSignal b) p / (p : ℂ) else 0) -
          (1 / 2 - 1 / (b : ℂ)) * (Real.log (Real.log x) : ℂ))) -
      (∑ p ∈ Finset.Ioc q ⌊x⌋₊, if p.Prime then (correctionTail b p : ℂ) else 0) := by
    have hs : (realPrimeTailSum (fun p => constructiveFluctuation b ell p / (p : ℝ)) q x : ℂ) =
        ((∑ p ∈ Finset.Ioc q ⌊x⌋₊,
          if p.Prime then unitExtension (allLagUnitTable b ell) p / (p : ℂ) else 0) -
        (∑ p ∈ Finset.Ioc q ⌊x⌋₊,
          if p.Prime then unitExtension (remainderClassSignal b) p / (p : ℂ) else 0)) -
        (∑ p ∈ Finset.Ioc q ⌊x⌋₊, if p.Prime then (correctionTail b p : ℂ) else 0) := by
      rw [ofReal_realPrimeTailSum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime
      · simp only [hprime, ↓reduceIte, Complex.ofReal_div, Complex.ofReal_natCast]
        exact constructive_prime_summand_eq hb hell hprime (Finset.mem_Ioc.mp hp).1
      · simp only [hprime, ↓reduceIte, sub_zero]
    rw [Complex.ofReal_add, hs]
    push_cast
    have hbne : (b : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne b
    field_simp [hbne]
    <;> ring
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  refine ⟨(LS - LR - LE).re, ?_⟩
  apply hr.congr'
  apply Filter.Eventually.of_forall
  intro x
  dsimp only [Function.comp_def]
  rw [← heq x, Complex.ofReal_re]

end NField.Alignment.CollisionPrimeLimits
