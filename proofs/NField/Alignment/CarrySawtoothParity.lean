/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-! # Reflection of the actual sawtooth character transform -/

namespace NField.Alignment.CarrySawtoothParity
open scoped BigOperators
open CollisionCharacterStructure CarryBoundarySpectra

/-- Title: `Reflection of the sawtooth character transform`. -/
theorem sawtooth_transform_reflection {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (ψ : Character m) : twistedTransform centeredSawtooth ψ 1 =
      -ψ (-1) * twistedTransform centeredSawtooth ψ 1 := by
  unfold twistedTransform
  simp only [one_mul]
  calc
    (∑ x : ZMod m, centeredSawtooth x * ψ x) =
        ∑ x : ZMod m, centeredSawtooth (-x) * ψ (-x) := by
      simpa using (Equiv.sum_comp (Equiv.neg (ZMod m))
        (fun x => centeredSawtooth x * ψ x)).symm
    _ = ∑ x : ZMod m, -ψ (-1) * (centeredSawtooth x * ψ x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [centeredSawtooth_neg hm, show -x = (-1) * x by ring, map_mul]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Title: `The sawtooth transform vanishes in every even channel`. -/
theorem sawtooth_even_transform_zero {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (ψ : Character m) (hψ : ψ.Even) : twistedTransform centeredSawtooth ψ 1 = 0 := by
  have h := sawtooth_transform_reflection hm ψ
  rw [show ψ (-1) = 1 from hψ] at h
  linear_combination (1 / 2 : ℂ) * h

end NField.Alignment.CarrySawtoothParity
