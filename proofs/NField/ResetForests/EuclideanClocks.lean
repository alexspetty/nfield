/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EuclideanArithmetic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-! # Every finite fold clock, including noncoprime states -/

set_option autoImplicit false

namespace NField.ResetForests.EuclideanFold

def FoldClock (N : ℕ) :=
  {s : Fin (N + 1) × Fin (N + 1) //
    2 ≤ s.1.val ∧ 1 ≤ s.2.val ∧ 2 * s.2.val ≤ s.1.val}

instance (N : ℕ) : DecidableEq (FoldClock N) := inferInstanceAs (DecidableEq (Subtype _))
instance (N : ℕ) : Fintype (FoldClock N) := inferInstanceAs (Fintype (Subtype _))

def clockDenominator {N : ℕ} (s : FoldClock N) : ℕ := s.val.1.val
def clockAddress {N : ℕ} (s : FoldClock N) : ℕ := s.val.2.val

def clockOfBounds (N d a : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N)
    (ha : 1 ≤ a) (had : 2 * a ≤ d) : FoldClock N :=
  ⟨(⟨d, by omega⟩, ⟨a, by omega⟩), ⟨hd, ha, had⟩⟩

theorem clock_of_bounds_coordinates (N d a : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N)
    (ha : 1 ≤ a) (had : 2 * a ≤ d) :
    clockDenominator (clockOfBounds N d a hd hdN ha had) = d ∧
      clockAddress (clockOfBounds N d a hd hdN ha had) = a := ⟨rfl, rfl⟩

theorem clock_bounds {N : ℕ} (s : FoldClock N) :
    2 ≤ clockDenominator s ∧ clockDenominator s ≤ N ∧
      1 ≤ clockAddress s ∧ 2 * clockAddress s ≤ clockDenominator s := by
  have h := s.property
  have hd := s.val.1.isLt
  dsimp [clockDenominator, clockAddress]
  omega

def clockHeight {N : ℕ} (s : FoldClock N) : ℕ :=
  remainderHeight (clockDenominator s) (clockAddress s)

def clockRemainder {N : ℕ} (s : FoldClock N) : ℤ :=
  signedRemainder (clockDenominator s) (clockAddress s)

def Nonterminal {N : ℕ} (s : FoldClock N) : Prop :=
  2 ≤ clockAddress s ∧ 0 < clockHeight s

instance {N : ℕ} (s : FoldClock N) : Decidable (Nonterminal s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem clock_height_half {N : ℕ} (s : FoldClock N) :
    2 * clockHeight s ≤ clockAddress s :=
  remainder_height_half _ _ (by have := clock_bounds s; omega)

theorem clock_half_interval {N : ℕ} (s : FoldClock N) :
    1 ≤ clockAddress s ∧ clockAddress s ≤ clockDenominator s / 2 := by
  have := clock_bounds s
  omega

theorem clock_address_strict {N : ℕ} (s : FoldClock N) :
    clockAddress s < clockDenominator s := by
  have := clock_bounds s
  omega

def successorClock {N : ℕ} (s : FoldClock N) (h : Nonterminal s) : FoldClock N :=
  ⟨(⟨clockAddress s, by have := clock_bounds s; omega⟩,
    ⟨clockHeight s, by have := clock_bounds s; have := clock_height_half s; omega⟩),
   ⟨h.1, h.2, clock_height_half s⟩⟩

theorem successor_coordinates {N : ℕ} (s : FoldClock N) (h : Nonterminal s) :
    clockDenominator (successorClock s h) = clockAddress s ∧
      clockAddress (successorClock s h) = clockHeight s := ⟨rfl, rfl⟩

theorem successor_strict_descent {N : ℕ} (s : FoldClock N) (h : Nonterminal s) :
    clockDenominator (successorClock s h) < clockDenominator s :=
  clock_address_strict s

theorem terminal_iff {N : ℕ} (s : FoldClock N) :
    ¬Nonterminal s ↔ clockAddress s = 1 ∨ clockRemainder s = 0 := by
  have := clock_bounds s
  simp only [Nonterminal, clockHeight, remainderHeight, clockRemainder,
    not_and_or, not_le, Nat.not_lt, Nat.le_zero_eq, Int.natAbs_eq_zero]
  omega

def clockSign {N : ℕ} (s : FoldClock N) : ℝ := (Int.sign (clockRemainder s) : ℤ)

theorem nonterminal_sign {N : ℕ} (s : FoldClock N) (h : Nonterminal s) :
    clockSign s = 1 ∨ clockSign s = -1 := by
  have hr : clockRemainder s ≠ 0 := by
    intro hr
    have ht : clockHeight s = 0 := by simpa [clockHeight, remainderHeight, clockRemainder] using congrArg Int.natAbs hr
    have := h.2
    omega
  rcases lt_or_gt_of_ne hr with hr | hr
  · right; simp [clockSign, Int.sign_eq_neg_one_of_neg hr]
  · left; simp [clockSign, Int.sign_eq_one_of_pos hr]

abbrev FoldSource (N : ℕ) := FoldClock N →₀ ℝ

noncomputable def clockBasis {N : ℕ} (s : FoldClock N) : FoldSource N := Finsupp.single s 1

noncomputable def clockImage {N : ℕ} (s : FoldClock N) : FoldSource N :=
  if h : Nonterminal s then clockSign s • clockBasis (successorClock s h) else 0

noncomputable def clockTransport (N : ℕ) : Module.End ℝ (FoldSource N) :=
  Finsupp.linearCombination ℝ clockImage

theorem transport_basis {N : ℕ} (s : FoldClock N) :
    clockTransport N (clockBasis s) = clockImage s := by
  simp [clockTransport, clockBasis]

theorem transport_nonterminal {N : ℕ} (s : FoldClock N) (h : Nonterminal s) :
    clockTransport N (clockBasis s) = clockSign s • clockBasis (successorClock s h) := by
  rw [transport_basis, clockImage, dif_pos h]

theorem transport_terminal {N : ℕ} (s : FoldClock N) (h : ¬Nonterminal s) :
    clockTransport N (clockBasis s) = 0 := by
  rw [transport_basis, clockImage, dif_neg h]

end NField.ResetForests.EuclideanFold
