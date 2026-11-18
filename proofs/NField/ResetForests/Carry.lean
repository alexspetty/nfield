/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetGram
import Mathlib
/-! # Integer phase lifts and midpoint carry work

The phase lift is proved for every real address, including resets. The
pointwise potential identity includes its extra midpoint term explicitly.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment.CollisionRampEnergy

theorem source_index_sum (s : ℕ) :
    (∑ j ∈ Finset.Icc 1 s, (j : ℝ)) = (s : ℝ)*((s : ℝ)+1)/2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ s+1), ih]
    push_cast
    ring

theorem midpoint_integer_row (j : ℕ) (x : ℝ) :
    2*(j : ℝ)*x-2*midpointRow j x =
      ((1+2*⌊(j : ℝ)*x⌋-(if Int.fract ((j : ℝ)*x) = 0 then 1 else 0) : ℤ) : ℝ) := by
  unfold midpointRow affineRow
  split_ifs with h
  · simp only [Int.fract] at h
    push_cast
    linarith
  · push_cast
    simp only [Int.fract]
    ring

/-- The exact integer phase lift, retaining all midpoint reset corrections. -/
theorem integer_phase_lift (s : ℕ) (x : ℝ) :
    (s : ℝ)*((s : ℝ)+1)*x-boundaryResponse s x =
      ((∑ j ∈ Finset.Icc 1 s,
        (1+2*⌊(j : ℝ)*x⌋-(if Int.fract ((j : ℝ)*x) = 0 then 1 else 0)) : ℤ) : ℝ) := by
  rw [show (s : ℝ)*((s : ℝ)+1)*x =
    ∑ j ∈ Finset.Icc 1 s, 2*(j : ℝ)*x by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, source_index_sum]
      ring]
  unfold boundaryResponse
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have h := midpoint_integer_row j x
  push_cast at h
  exact h

def carryMoment (u : ℝ) (w : ℤ) : ℝ :=
  (w : ℝ)*((w : ℝ)+1-2*u)/2

theorem carry_moment_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (w : ℤ) :
    0 ≤ carryMoment u w := by
  unfold carryMoment
  apply div_nonneg _ (by norm_num)
  rcases lt_trichotomy w 0 with hw | hw | hw
  · have hwl : (w : ℝ) ≤ -1 := by exact_mod_cast (show w ≤ -1 by omega)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · simp [hw]
  · have hwl : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    exact mul_nonneg (by linarith) (by linarith)

def periodicPotential (y : ℝ) : ℝ := (Int.fract y^2-Int.fract y)/2

/-- The midpoint term is present even when a transported phase is integral. -/
theorem carry_potential_identity {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (v : ℝ) :
    v*midpointRow 1 (u+v) =
      periodicPotential (u+v)-periodicPotential u + v^2/2 -
        carryMoment u ⌊u+v⌋ +
        (if Int.fract (u+v) = 0 then v/2 else 0) := by
  unfold midpointRow affineRow periodicPotential carryMoment
  simp only [Nat.cast_one, one_mul, Int.fract_eq_self.mpr ⟨hu0, hu1⟩]
  split_ifs with h
  · have hw : (⌊u+v⌋ : ℝ) = u+v := by
      simp only [Int.fract] at h
      linarith
    simp only [h, zero_pow (by decide : 2 ≠ 0), sub_self, zero_div, mul_zero]
    rw [hw]
    ring
  · simp only [Int.fract]
    ring

/-- The reciprocal second difference in the actual lifted angle. -/
theorem reciprocal_angle_curvature {k : ℝ} (hk : 0 < k) (Q A : ℝ) :
    Q*A/(k+2)-2*(Q*A/(k+1))+Q*A/k =
      2*Q*A/(k*(k+1)*(k+2)) := by
  have h0 : k ≠ 0 := hk.ne'
  have h1 : k+1 ≠ 0 := by linarith
  have h2 : k+2 ≠ 0 := by linarith
  field_simp
  ring

/-- Both ordered source/phase terms and the measure change are retained. -/
theorem measured_branch_connection {ι : Type*} (s : Finset ι)
    (μ μnext v vnext φ φnext : ι → ℝ) :
    (∑ a ∈ s, μnext a*vnext a*φnext a) -
        (∑ a ∈ s, μ a*v a*φ a) =
      (∑ a ∈ s, μ a*((vnext a-v a)*φ a +
        v a*(φnext a-φ a)+(vnext a-v a)*(φnext a-φ a))) +
      ∑ a ∈ s, (μnext a-μ a)*vnext a*φnext a := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end NField.ResetForests.Core
