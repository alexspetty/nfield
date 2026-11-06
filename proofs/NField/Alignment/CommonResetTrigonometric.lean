/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSineEndpoint

/-! # The literal asymmetric sine endpoints -/

noncomputable section

namespace NField.Alignment.CommonResetTrigonometric

open scoped BigOperators
open CommonResetLift CommonResetEndpoint CommonResetHalfFrequencies CommonResetSineEndpoint

theorem zero_period_prefix (f : ℕ → ℝ) {t : ℕ}
    (hperiod : ∀ a, f (a+t) = f a) (hzero : f 0 = 0)
    (hblock : (∑ a ∈ Finset.range t, f a) = 0) (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, f a) = ∑ a ∈ Finset.Icc 1 (N%t), f a := by
  have hs := sum_real_periodic_blocks (k := t) (fun a => f (a+1))
    (fun a => by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod (a+1))
    (N/t) (N%t)
  have shift (n : ℕ) : (∑ a ∈ Finset.range n, f (a+1)) = ∑ a ∈ Finset.Icc 1 n, f a := by
    have hset : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by ext a; simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm]
  have hb : (∑ a ∈ Finset.range t, f (a+1)) = 0 := by
    have htel := Finset.sum_range_succ' f t
    rw [Finset.sum_range_succ, hzero, add_zero] at htel
    have htzero : f t = 0 := by simpa only [zero_add, hzero] using hperiod 0
    rw [htzero, add_zero] at htel
    exact htel.symm.trans hblock
  rw [show N/t*t+N%t=N by simpa only [Nat.mul_comm] using Nat.div_add_mod N t,
    hb, mul_zero, zero_add, shift, shift] at hs
  exact hs

theorem sinePrefix_mod {t : ℕ} [NeZero t] (N : ℕ) (j : ZMod t) :
    sinePrefix N j = sinePrefix (N%t) j := by
  apply zero_period_prefix
  · intro a
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  · simp [characterSine]
  · have hz : (∑ a : ZMod t, characterSine (a*j)) = 0 := by
      have he := Equiv.sum_comp (Equiv.neg (ZMod t)) (fun a : ZMod t => characterSine (a*j))
      simp only [Equiv.neg_apply, neg_mul, characterSine_odd, Finset.sum_neg_distrib] at he
      linarith
    have hg := CommonResetGrid.sum_residue_values (m := t)
      (fun a : ℕ => characterSine ((a : ZMod t)*j))
    simp only [ZMod.natCast_zmod_val] at hg
    rw [← hg]
    exact hz

theorem characterSine_nat_mul {t : ℕ} [NeZero t] (a : ℕ) (j : ZMod t) :
    characterSine ((a : ZMod t)*j) =
      Real.sin (2*Real.pi*(a : ℝ)*(j.val : ℝ)/(t : ℝ)) := by
  have he : ZMod.stdAddChar ((a : ZMod t)*j) =
      Complex.exp (Complex.ofReal (2*Real.pi*(a : ℝ)*(j.val : ℝ)/(t : ℝ))*Complex.I) := by
    nth_rw 1 [← ZMod.natCast_zmod_val j]
    rw [← Nat.cast_mul]
    rw [show ((a*j.val : ℕ) : ZMod t) = ((a*j.val : ℤ) : ZMod t) by simp,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  unfold characterSine
  rw [he, Complex.exp_ofReal_mul_I_im]

theorem sine_prefix_product (θ : ℝ) (N : ℕ) :
    Real.sin θ*(∑ a ∈ Finset.Icc 1 N, Real.sin (2*(a : ℝ)*θ)) =
      Real.sin ((N : ℝ)*θ)*Real.sin (((N : ℝ)+1)*θ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1), mul_add, ih]
    push_cast
    have hleft : (N : ℝ)*θ = (((N : ℝ)+1)*θ)-θ := by ring
    have hright : ((N : ℝ)+1+1)*θ = (((N : ℝ)+1)*θ)+θ := by ring
    have htwice : 2*((N : ℝ)+1)*θ = 2*(((N : ℝ)+1)*θ) := by ring
    rw [hleft, hright, htwice, Real.sin_sub, Real.sin_add, Real.sin_two_mul]
    ring

/-- Title: `The sine prefix keeps the actual clock endpoints N and N plus one`. -/
theorem sinePrefix_closed {t : ℕ} [NeZero t] (N : ℕ) (j : ZMod t)
    (hj : j ∈ lowerResidues t) :
    sinePrefix N j =
      Real.sin (Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ))*
        Real.sin (Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ))/
          Real.sin (Real.pi*(j.val : ℝ)/(t : ℝ)) := by
  have hjd := (Finset.mem_filter.mp hj).2
  have htR : (0 : ℝ) < t := by exact_mod_cast NeZero.pos t
  have hjR : (0 : ℝ) < j.val := by exact_mod_cast hjd.1
  have hjt : (j.val : ℝ) < t := by exact_mod_cast j.val_lt
  let θ : ℝ := Real.pi*(j.val : ℝ)/(t : ℝ)
  have hθ : 0 < θ := div_pos (mul_pos Real.pi_pos hjR) htR
  have hθπ : θ < Real.pi := by
    apply (div_lt_iff₀ htR).mpr
    exact mul_lt_mul_of_pos_left hjt Real.pi_pos
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
  have hp := sine_prefix_product θ N
  have he : sinePrefix N j = ∑ a ∈ Finset.Icc 1 N, Real.sin (2*(a : ℝ)*θ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [characterSine_nat_mul]
    congr 1
    dsimp [θ]
    ring
  rw [← he] at hp
  apply (eq_div_iff hsin).mpr
  have h1 : Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ) = (N : ℝ)*θ := by dsimp [θ]; ring
  have h2 : Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ) = ((N : ℝ)+1)*θ := by dsimp [θ]; ring
  rw [h1, h2]
  simpa only [mul_comm] using hp

/-- Title: `The endpoint response has the complete printed sine quotient`. -/
theorem endpoint_literal_sine {t : ℕ} [NeZero t] (N : ℕ) (x : ZMod t) :
    endpointDifference (N%t) x = (4/(t : ℝ))*
      ∑ j ∈ lowerResidues t,
        (Real.sin (Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ))*
          Real.sin (Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ))/
            Real.sin (Real.pi*(j.val : ℝ)/(t : ℝ)))*
        Real.sin (2*Real.pi*(j.val : ℝ)*(x.val : ℝ)/(t : ℝ)) := by
  rw [endpoint_half_sine (N%t) (Nat.mod_lt N (NeZero.pos t))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← sinePrefix_mod N j, sinePrefix_closed N j hj]
  have hs := characterSine_nat_mul j.val x
  simpa only [ZMod.natCast_zmod_val] using congrArg
    (fun z : ℝ => (Real.sin (Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ))*
      Real.sin (Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ))/
        Real.sin (Real.pi*(j.val : ℝ)/(t : ℝ)))*z) hs

end NField.Alignment.CommonResetTrigonometric
