/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDyadicBlockConcentration

/-!
# Explicit square-root sums for the return-time estimate
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRootSumBounds

open scoped BigOperators

theorem inverse_sqrt_step (k : ℕ) :
    1/Real.sqrt (k+1 : ℕ)≤2*(Real.sqrt (k+1 : ℕ)-Real.sqrt (k : ℝ)) := by
  have hk : (0 : ℝ)<(k+1 : ℕ) := by exact_mod_cast (show 0<k+1 by omega)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hk)).mpr
  have h0 := Real.sq_sqrt (Nat.cast_nonneg k)
  have h1 := Real.sq_sqrt hk.le
  push_cast at h1 ⊢
  nlinarith [sq_nonneg (Real.sqrt ((k : ℝ)+1)-Real.sqrt (k : ℝ))]

theorem inverse_sqrt_sum (N : ℕ) :
    (∑ k∈Finset.range N, 1/Real.sqrt (k+1 : ℕ))≤2*Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := inverse_sqrt_step N
    nlinarith

theorem sqrt_ratio_sum {L : ℝ} (hL : 0≤L) (N : ℕ) :
    (∑ k∈Finset.range N, Real.sqrt (L/(k+1 : ℕ)))≤
      2*Real.sqrt L*Real.sqrt (N : ℝ) := by
  simp_rw [Real.sqrt_div hL]
  calc
    _ = Real.sqrt L*(∑ k∈Finset.range N, 1/Real.sqrt (k+1 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ Real.sqrt L*(2*Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_sqrt_sum N) (Real.sqrt_nonneg L)
    _ = _ := by ring

theorem reciprocal_le_sqrt_ratio {L : ℝ} (hL : 1≤L) {N : ℕ} (hN : 0<N) :
    1/(N : ℝ)≤Real.sqrt (L/(N : ℝ)) := by
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  have hp : (0 : ℝ)<N := by linarith
  have hq : 0≤L/(N : ℝ) := div_nonneg (by linarith) hp.le
  have hs := Real.sq_sqrt hq
  have hsmall : 1/(N : ℝ)≤1 := (div_le_one hp).mpr hn
  have hle : 1/(N : ℝ)≤L/(N : ℝ) := div_le_div_of_nonneg_right hL hp.le
  nlinarith [Real.sqrt_nonneg (L/(N : ℝ)),div_nonneg (by norm_num : (0 : ℝ)≤1) hp.le]

end NField.Alignment.CollisionRootSumBounds
