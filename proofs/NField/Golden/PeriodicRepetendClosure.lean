/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RepetendClosure
import NField.Golden.PeriodicRepetendRigidity

/-!
# Cumulative closure at the rational golden endpoints

The established arbitrary-period rational classification forces a primitive
period of one and the modulus-two or modulus-three endpoint. The actual
reference tail and every accepted cyclic shift then have cumulative closure
length equal to that modulus at every valid common clearing depth. This is
Corollary 14 of "Repetend Rigidity at the Golden Scale".
-/

namespace NField.Golden
open NField.Alignment

/-- At the two rational golden-power endpoints, closure of the actual cleared
reference and every accepted cyclic shift equals the classified modulus two
or three. No closure formula is built into the digit-stream definition. -/
theorem rational_endpoint_cumulative_closure {b q r m D : ℕ} {lambda : ℚ}
    (hb : 2 ≤ b) (hq : 2 ≤ q) (hr : 1 ≤ r) (hm : 0 < m)
    (hcop : Nat.Coprime q b) (hD : m ∣ b ^ D)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (heq : orbitReferenceInterpolant q (coprimeBasePeriod b q hcop) (lambda : ℝ)
      ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal) :
    ((q=2 ∧ lambda=0 ∧ r=2) ∨ (q=3 ∧ lambda=1 ∧ r=2)) ∧
    cumulativeClosureLengthAtDepth b (q*m) 1 D = q ∧
    (∀ k, CyclicShiftAtDepth b q m D k →
      cumulativeClosureLengthAtDepth b (q*m) k D = q) := by
  obtain ⟨hbmod, hend⟩ := (orbit_rational_period_rigidity hb hq hr hcop hl0 hl1).mp heq
  have hperiod := (coprimeBasePeriod_eq_one_iff (by omega) hcop).mpr hbmod
  exact ⟨hend, cyclic_shift_closure_period_one hb (by omega) hm hcop hD hperiod⟩

end NField.Golden
