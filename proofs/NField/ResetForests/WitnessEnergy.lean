/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactProjection
/-! # Source energy from its exact paired-row witness -/

set_option autoImplicit false

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix

theorem paired_witness_energy {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ)
    (z : Fin N → ℚ) (R : ℕ → Bool → Fin N → ℚ)
    (w : ℕ → Bool → ℚ) (C : Finset ℕ)
    (hz : G *ᵥ z = fun j => ∑ k ∈ C,
      (R k false j * w k false + R k true j * w k true))
    (hc : ∀ k ∈ C, ∀ b, R k b ⬝ᵥ z = R k b ⬝ᵥ (fun _ => 1)) :
    z ⬝ᵥ (G *ᵥ z) = ∑ k ∈ C,
      ((R k false ⬝ᵥ (fun _ => 1)) * w k false +
       (R k true ⬝ᵥ (fun _ => 1)) * w k true) := by
  rw [hz]
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hf := hc k hk false
  have ht := hc k hk true
  dsimp only [dotProduct] at hf ht
  rw [← hf, ← ht, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end NField.ResetForests.ExactCost
