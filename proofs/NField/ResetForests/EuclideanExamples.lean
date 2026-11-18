/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EuclideanWeights
/-! # A noncoprime edge and an actual accumulation at a terminal clock -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.EuclideanFold

def clock21 : FoldClock 7 := clockOfBounds 7 2 1 (by decide) (by decide) (by decide) (by decide)
def clock52 : FoldClock 7 := clockOfBounds 7 5 2 (by decide) (by decide) (by decide) (by decide)
def clock72 : FoldClock 7 := clockOfBounds 7 7 2 (by decide) (by decide) (by decide) (by decide)
def clock104 : FoldClock 10 := clockOfBounds 10 10 4 (by decide) (by decide) (by decide) (by decide)
def clock42 : FoldClock 10 := clockOfBounds 10 4 2 (by decide) (by decide) (by decide) (by decide)

theorem literal_half_tie : nearestQuotient 10 4 = 2 ∧ signedRemainder 10 4 = 2 := by
  decide

theorem noncoprime_clock_exists :
    clockDenominator clock104 = 10 ∧ clockAddress clock104 = 4 ∧ Nat.gcd 10 4 = 2 := by
  decide

theorem noncoprime_transport_edge :
    clockTransport 10 (clockBasis clock104) = clockBasis clock42 := by
  have h : Nonterminal clock104 := by decide
  have he : successorClock clock104 h = clock42 := rfl
  have hs : clockSign clock104 = 1 := by norm_num [clockSign, clockRemainder,
    clock104, clockOfBounds, clockDenominator, clockAddress, signedRemainder, nearestQuotient]
  rw [transport_nonterminal clock104 h, he, hs, one_smul]

theorem inverse_clock52 :
    foldInverse 7 (clockBasis clock52) = clockBasis clock52 - clockBasis clock21 := by
  have h : Nonterminal clock52 := by decide
  have he : successorClock clock52 h = clock21 := rfl
  have hs : clockSign clock52 = 1 := by norm_num [clockSign, clockRemainder,
    clock52, clockOfBounds, clockDenominator, clockAddress, signedRemainder, nearestQuotient]
  rw [inverse_basis_recursion clock52 h, he, hs,
    inverse_terminal_basis clock21 (by decide), one_smul]

theorem inverse_clock72 :
    foldInverse 7 (clockBasis clock72) = clockBasis clock72 - clockBasis clock21 := by
  have h : Nonterminal clock72 := by decide
  have he : successorClock clock72 h = clock21 := rfl
  have hs : clockSign clock72 = 1 := by norm_num [clockSign, clockRemainder,
    clock72, clockOfBounds, clockDenominator, clockAddress, signedRemainder, nearestQuotient]
  rw [inverse_basis_recursion clock72 h, he, hs,
    inverse_terminal_basis clock21 (by decide), one_smul]

theorem accumulated_terminal_coefficient :
    (foldInverse 7 (clockBasis clock52 + clockBasis clock72)) clock21 = -2 := by
  rw [map_add, inverse_clock52, inverse_clock72]
  have h52 : clock52 ≠ clock21 := by decide
  have h72 : clock72 ≠ clock21 := by decide
  norm_num [clockBasis, Finsupp.single_apply, h52, h72, Ne.symm h52, Ne.symm h72]

theorem accumulated_coefficient_exceeds_one :
    1 < |(foldInverse 7 (clockBasis clock52 + clockBasis clock72)) clock21| := by
  rw [accumulated_terminal_coefficient]
  norm_num

end NField.ResetForests.EuclideanFold
