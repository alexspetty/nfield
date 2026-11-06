/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealCollisionPrimeLimits
import NField.Alignment.PrimeRemainderMean
import NField.Alignment.CollisionCorrectionTail
import NField.Alignment.BinDerangementsClosure

/-! # The literal constructive-mean fluctuation and its prime summand identity -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.BinDerangementsClosure

def constructiveFluctuation (b ell n : ℕ) : ℝ :=
  (directAllLagCollisionCount b ell n : ℝ) -
    (constructiveMeanValue b ((n - 1) / b) ((n - 1) % b) : ℝ)

theorem quotient_correction_denominator {b n : ℕ} (hb : 0 < b) (hn : b + 1 < n) :
    n - b - 1 = b * ((n - 1) / b - 1) + (n - 1) % b := by
  have hQ : 1 ≤ (n - 1) / b := (Nat.le_div_iff_mul_le hb).mpr (by omega)
  have hdivision := Nat.mod_add_div (n - 1) b
  have hmul : b * ((n - 1) / b) = b * ((n - 1) / b - 1) + b := by
    calc
      b * ((n - 1) / b) = b * (((n - 1) / b - 1) + 1) := by rw [Nat.sub_add_cancel hQ]
      _ = _ := by ring
  rw [hmul] at hdivision
  omega

theorem constructiveFluctuation_div_identity {b ell n : ℕ} (hb : 2 ≤ b)
    (hn : b + 1 < n) :
    constructiveFluctuation b ell n / (n : ℝ) =
      (directAllLagDeviation b ell n : ℝ) / n -
        (((n - 1) % b : ℕ) : ℝ) / ((b : ℝ) * n) - correctionTail b n := by
  let Q := (n - 1) / b
  let R := (n - 1) % b
  let N := n - b - 1
  have hb0 : 0 < b := by omega
  have hN : 0 < N := by dsimp [N]; omega
  have hR : R < b := Nat.mod_lt _ hb0
  have hden : N = b * (Q - 1) + R := quotient_correction_denominator hb0 hn
  have hmeanQ := constructiveMeanValue_eq_quotient_plus_correction
    (b := b) (Q := Q) (R := R) (by omega)
  rw [← hden] at hmeanQ
  have hmean := congrArg (fun z : ℚ => (z : ℝ)) hmeanQ
  push_cast at hmean
  have hrelation : N + b = b * Q + R := by
    have hd := Nat.mod_add_div (n - 1) b
    dsimp [N, Q, R]
    omega
  have hcorQ := correction_expansion hb0 hN hR hrelation
  have hcor := congrArg (fun z : ℚ => (z : ℝ)) hcorQ
  push_cast at hcor
  rw [Nat.cast_sub hR.le] at hcor
  have hNreal : (N : ℝ) = (n : ℝ) - b - 1 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 1 ≤ n - b), Nat.cast_sub (by omega : b ≤ n)]
    norm_num
  change ((directAllLagCollisionCount b ell n : ℝ) - (constructiveMeanValue b Q R : ℝ)) / n = _
  rw [hmean, hcor, hNreal]
  simp only [directAllLagDeviation, Int.cast_sub, Int.cast_natCast, correctionTail]
  dsimp [Q, R]
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hNne : (n : ℝ) - b - 1 ≠ 0 := by
    have h : (b : ℝ) + 1 < n := by exact_mod_cast hn
    linarith
  field_simp [hbne, hnne, hNne]
  <;> ring

theorem prime_unit_of_modulus_lt {q n : ℕ} [NeZero q]
    (hp : n.Prime) (hn : q < n) : IsUnit (n : ZMod q) := by
  apply (ZMod.isUnit_iff_coprime n q).mpr
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hle := Nat.le_of_dvd (NeZero.pos q) hdiv
  omega

theorem pred_mod_eq_unit_remainder {b n : ℕ} [NeZero b] (hb : 2 ≤ b)
    (hunit : IsUnit (n : ZMod b)) : (n - 1) % b = n % b - 1 := by
  have hcop : n.Coprime b := (ZMod.isUnit_iff_coprime n b).mp hunit
  have hmod : (n % b).Coprime b := (ZMod.coprime_mod_iff_coprime n b).mpr hcop
  have hr : 1 ≤ n % b := by
    by_contra h
    have hz : n % b = 0 := by omega
    rw [hz] at hmod
    simp only [Nat.coprime_zero_left] at hmod
    omega
  have hrep : n - 1 = b * (n / b) + (n % b - 1) := by
    have h := Nat.mod_add_div n b
    omega
  rw [hrep, Nat.mul_add_mod, Nat.mod_eq_of_lt]
  have h := Nat.mod_lt n (NeZero.pos b)
  omega

end NField.Alignment.CollisionPrimeLimits
