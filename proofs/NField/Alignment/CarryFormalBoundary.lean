/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-! # Formal interval endpoints before cyclic cancellation -/

namespace NField.Alignment.CarryFormalBoundary
open scoped BigOperators
open CarryBoundarySpectra

/-- Each interval is represented by its first cell and its number of cells.
The two signed endpoints are retained with multiplicity. -/
def formalIntervalBoundary (intervals : List (ℕ × ℕ)) : List (ℕ × ℤ) :=
  intervals.flatMap fun I => [(I.1, -1), (I.1 + I.2, 1)]

/-- Title: `The formal boundary has two endpoints per interval`. -/
theorem formal_boundary_endpoint_count (intervals : List (ℕ × ℕ)) :
    (formalIntervalBoundary intervals).length = 2 * intervals.length := by
  induction intervals with
  | nil => rfl
  | cons I intervals ih =>
      simp only [formalIntervalBoundary, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at *
      omega

/-- Title: `Formal endpoint flux equals the sum of cell differences`. -/
theorem formal_boundary_stokes (intervals : List (ℕ × ℕ)) (f : ℕ → ℂ) :
    ((formalIntervalBoundary intervals).map (fun e => (e.2 : ℂ) * f e.1)).sum =
      (intervals.map fun I => ∑ j ∈ Finset.range I.2,
        (f (I.1 + j + 1) - f (I.1 + j))).sum := by
  induction intervals with
  | nil => rfl
  | cons I intervals ih =>
      simp only [formalIntervalBoundary, List.flatMap_cons, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at *
      rw [intervalStokes, ← ih]
      push_cast
      ring

end NField.Alignment.CarryFormalBoundary
