/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.CollisionMap
/-! # The complete source form keeps both carrier sectors -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.GramDecomposition

open scoped BigOperators Matrix
open NField.Alignment CollisionBernoulliStraightening SourceMetrics

def unitGram (N p : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ a : Fin (p^2), if ¬p ∣ a.val then
    samplingMatrix N (p^2) a i*samplingMatrix N (p^2) a j else 0

theorem complete_gram_sector_split (N p : ℕ) :
    sampledGram N (p^2)=unitGram N p+nonunitGram N p := by
  ext i j
  simp only [sampledGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, unitGram, nonunitGram, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hd : p ∣ a.val <;> simp [hd]

theorem complete_mixed_sector_split (N p : ℕ) (c e : Fin N → ℝ) :
    c ⬝ᵥ (sampledGram N (p^2) *ᵥ e)=
      c ⬝ᵥ (unitGram N p *ᵥ e)+c ⬝ᵥ (nonunitGram N p *ᵥ e) := by
  rw [complete_gram_sector_split, Matrix.add_mulVec, dotProduct_add]

theorem nonunit_gram_is_nonzero {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    nonunitGram (p-1) p ≠ 0 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : (0 : ℝ) < ((p-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p-1)
  have h2 : (0 : ℝ) < (p : ℝ)-2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have htrace : 0 < Matrix.trace (nonunitGram (p-1) p) := by
    rw [nonunit_gram_trace hp]
    positivity
  intro hz
  rw [hz, Matrix.trace_zero] at htrace
  exact (lt_irrefl 0) htrace

theorem collision_energy_unit_sector {p : ℕ} (hp : p.Prime) :
    collisionEnergy hp=(fun _ => (1 : ℝ)) ⬝ᵥ
      (unitGram (p-1) p *ᵥ (fun _ => (1 : ℝ))) := by
  rw [(collision_energy_complete_readings hp).2, complete_mixed_sector_split,
    nonunit_gram_annihilates_complete hp, dotProduct_zero, add_zero]

end NField.ResetForests.GramDecomposition
