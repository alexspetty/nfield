/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Golden.WeightedRepetendRigidity

/-!
# Finite replication and identifiable weights

The actual weighted denominator score determines its real weight when the
terminating block is nonempty. This records the m = 1 exception and the
rationality boundary using the existing score, without defining a surrogate.
-/

namespace NField.Golden

/-- At scale one there are no terminating rows, so the score is independent
of their weight. -/
theorem weightedReferenceScore_one {q : ℕ} (hq : 1 < q) (lambda : ℝ) :
    weightedReferenceScore q 1 lambda = 1 / ((q - 1 : ℕ) : ℝ) := by
  simp [weightedReferenceScore_eq hq]

/-- Once the terminating block is nonempty, the actual finite score determines
its weight uniquely. -/
theorem weightedReferenceScore_injective {q m : ℕ} (hq : 1 < q)
    (hm : 1 < m) : Function.Injective (weightedReferenceScore q m) := by
  have hqm : 4 ≤ q * m := Nat.mul_le_mul hq hm
  have hrows : 0 < q * m - 1 := by omega
  have hrowsR : ((q * m - 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have htermR : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show m - 1 ≠ 0 by omega)
  intro lambda mu heq
  rw [weightedReferenceScore_eq hq, weightedReferenceScore_eq hq] at heq
  have hnum := congrArg (fun x : ℝ => x * ((q * m - 1 : ℕ) : ℝ)) heq
  simp only [div_mul_cancel₀ _ hrowsR] at hnum
  exact mul_right_cancel₀ htermR (add_right_cancel hnum)

/-- For a nonempty terminating block, an irrational weight gives an irrational
finite score and conversely. In particular it cannot equal a finite marked-copy
proportion, since such a proportion is rational. -/
theorem weightedReferenceScore_irrational_iff {q m : ℕ} (hq : 1 < q)
    (hm : 1 < m) (lambda : ℝ) :
    Irrational (weightedReferenceScore q m lambda) ↔ Irrational lambda := by
  rw [weightedReferenceScore_eq hq]
  have hqm : 4 ≤ q * m := Nat.mul_le_mul hq hm
  have hrows : q * m - 1 ≠ 0 := by omega
  have hterm : m - 1 ≠ 0 := by omega
  simp [irrational_div_natCast_iff, irrational_add_natCast_iff,
    irrational_mul_natCast_iff, hrows, hterm]

end NField.Golden
