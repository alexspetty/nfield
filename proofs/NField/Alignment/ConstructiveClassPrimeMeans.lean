/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CoarsePrimeMeans

/-! # The actual limiting constructive fluctuation mean in each coarse prime class -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionTransformStrip

def coarsePrimeCount {b : ℕ} (u : (ZMod b)ˣ) (c : ℕ) (x : ℝ) : ℝ :=
  realPrimeTailSum (fun p => if (p : ZMod b) = u then 1 else 0) c x

theorem unit_delta_extension {b : ℕ} [NeZero b] (u : (ZMod b)ˣ) (p : ℕ) :
    unitExtension (fun a => if a = u then (1 : ℂ) else 0) p =
      if (p : ZMod b) = u then 1 else 0 := by
  classical
  by_cases hp : IsUnit (p : ZMod b)
  · have hc : hp.unit = u ↔ (p : ZMod b) = u := by rw [Units.ext_iff, hp.unit_spec]
    simp only [unitExtension, dif_pos hp, hc]
  · have hc : (p : ZMod b) ≠ u := by
      intro h
      apply hp
      rw [h]
      exact u.isUnit
    simp only [unitExtension, dif_neg hp, if_neg hc]

theorem coarse_prime_count_density {b : ℕ} [NeZero b] (u : (ZMod b)ˣ) (c : ℕ) :
    Tendsto (fun x : ℝ => coarsePrimeCount u c x / (Nat.primeCounting ⌊x⌋₊ : ℝ))
      atTop (𝓝 (b.totient : ℝ)⁻¹) := by
  classical
  have h := periodic_prime_tail_pi_limit (fun a => if a = u then (1 : ℂ) else 0) c
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  have heq (x : ℝ) : (coarsePrimeCount u c x : ℂ) =
      ∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime then
        unitExtension (fun a => if a = u then (1 : ℂ) else 0) p else 0 := by
    simp only [coarsePrimeCount, ofReal_realPrimeTailSum, unit_delta_extension,
      apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
  convert hr using 1
  · ext x
    simp only [Function.comp_apply]
    rw [← heq]
    simp
  · simp

def coarseConstructiveMean {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : (ZMod b)ˣ) : ℝ :=
  fiberMean (coarseUnitReduction b ell) (realUnitCollisionTable b ell) u -
    (((u : ZMod b).val : ℝ) - 1) / b

theorem constructive_fluctuation_coarse_identity {b ell p : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : p.Prime) (hbp : b + 1 < p) (u : (ZMod b)ˣ) (hclass : (p : ZMod b) = u) :
    constructiveFluctuation b ell p = realDirectCenteredCollisionValue b ell p +
      coarseConstructiveMean (ell := ell) u - (p : ℝ) * correctionTail b p := by
  have hq := prime_unit_at_all_lag_modulus (ell := ell) (by omega : 0 < b) hp (by omega)
  have hub := prime_unit_of_modulus_lt hp (by omega : b < p)
  have hunit : hub.unit = u := by
    apply Units.ext
    rw [hub.unit_spec, hclass]
  have hred : coarseUnitReduction b ell hq.unit = u :=
    (coarse_reduction_prime_unit hq hub).trans hunit
  have hmod : p % b = (u : ZMod b).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hclass
  have huval : 1 ≤ (u : ZMod b).val := by
    have hcop : (u : ZMod b).val.Coprime b :=
      (ZMod.isUnit_iff_coprime _ _).mp (by simpa using u.isUnit)
    by_contra h
    have hz : (u : ZMod b).val = 0 := by omega
    rw [hz] at hcop
    simp only [Nat.coprime_zero_left] at hcop
    omega
  have hR : (((p - 1) % b : ℕ) : ℝ) = ((u : ZMod b).val : ℝ) - 1 := by
    rw [pred_mod_eq_unit_remainder hb hub, hmod, Nat.cast_sub huval]
    norm_num
  have hbase := constructiveFluctuation_div_identity (ell := ell) hb hbp
  rw [div_mul_eq_div_div] at hbase
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hi := congrArg (fun z : ℝ => z * p) hbase
  simp only [sub_mul, div_mul_cancel₀ _ hpne] at hi
  rw [hR] at hi
  rw [realDirectCenteredCollisionValue, dif_pos hq, hred, coarseConstructiveMean]
  linarith

/-- Title: `Each coarse prime class has its exact limiting constructive mean`.
The denominator counts the actual primes in the class, and the finite correction
is removed using Mathlib's weighted Cesaro theorem. -/
theorem constructive_class_prime_mean_limit {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (u : (ZMod b)ˣ) (c : ℕ) (hc : b + 1 ≤ c) :
    Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => if (p : ZMod b) = u then constructiveFluctuation b ell p else 0) c x /
        coarsePrimeCount u c x) atTop (𝓝 (coarseConstructiveMean (ell := ell) u)) := by
  classical
  let M := coarseConstructiveMean (ell := ell) u
  have hz := coarse_centered_prime_average_zero hb hell u c (by omega)
  have hn := coarse_prime_count_density u c
  have he := filtered_vanishing_prime_tail_average (unweighted_correction_tendsto_zero hb)
    (fun p => (p : ZMod b) = u) c
  have hsum := (hz.add (hn.const_mul M)).sub he
  simp only [zero_add, sub_zero] at hsum
  have hidentity (x : ℝ) :
      realPrimeTailSum (fun p => if (p : ZMod b) = u then constructiveFluctuation b ell p else 0) c x =
      realPrimeTailSum (fun p => if (p : ZMod b) = u then realDirectCenteredCollisionValue b ell p else 0) c x +
        M * coarsePrimeCount u c x -
          realPrimeTailSum (fun p => if (p : ZMod b) = u then (p : ℝ) * correctionTail b p else 0) c x := by
    simp only [realPrimeTailSum, coarsePrimeCount, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hmem
    by_cases hp : p.Prime
    · by_cases hclass : (p : ZMod b) = u
      · simp only [hp, hclass, ↓reduceIte, mul_one]
        exact constructive_fluctuation_coarse_identity hb hell hp
          (hc.trans_lt (mem_Ioc.mp hmem).1) u hclass
      · simp [hp, hclass]
    · simp [hp]
  have hnorm : Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => if (p : ZMod b) = u then constructiveFluctuation b ell p else 0) c x /
        (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 (M * (b.totient : ℝ)⁻¹)) := by
    apply hsum.congr'
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    rw [hidentity]
    ring
  have hbphi : (b.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos b)).ne'
  have h := hnorm.div hn (inv_ne_zero hbphi)
  rw [mul_div_cancel_right₀ M (inv_ne_zero hbphi)] at h
  apply h.congr'
  filter_upwards [(Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop).eventually
    (eventually_ge_atTop 1)] with x hx
  change 1 ≤ Nat.primeCounting ⌊x⌋₊ at hx
  have hpne : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting ⌊x⌋₊ ≠ 0 by omega)
  exact div_div_div_cancel_right₀ hpne _ _

end NField.Alignment.CollisionPrimeLimits
