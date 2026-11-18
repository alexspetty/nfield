/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EnteringSource
/-! # Unique minimum-work lifts of attainable record readings -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_work_nonnegative (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (x : Fin N → ℝ) : 0 ≤ sourceWork G x x := by
  by_cases hx : x = 0
  · simp [sourceWork, hx]
  · simpa only [sourceWork, star_trivial] using (hG.dotProduct_mulVec_pos hx).le

theorem source_work_zero_iff (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (x : Fin N → ℝ) : sourceWork G x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hn
    have hp : 0 < sourceWork G x x := by
      simpa only [sourceWork, star_trivial] using hG.dotProduct_mulVec_pos hn
    linarith
  · intro hx
    simp [sourceWork, hx]

theorem record_lift_pythagoras (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c d : Fin N → ℝ) (hd : A *ᵥ d = A *ᵥ c) :
    sourceWork G d d = sourceWork G (oldSource G hG A c) (oldSource G hG A c) +
      sourceWork G (d - oldSource G hG A c) (d - oldSource G hG A c) := by
  have hk : A *ᵥ (d - oldSource G hG A c) = 0 := by
    rw [Matrix.mulVec_sub, hd, old_source_reading, sub_self]
  have ho : sourceWork G (oldSource G hG A c) (d - oldSource G hG A c) = 0 :=
    lifted_kernel_work_zero G hG A _ _ hk
  have he := PacketQueries.symmetric_query_add G (hermitian_transpose G hG.1)
    (oldSource G hG A c) (d - oldSource G hG A c)
  have hs : oldSource G hG A c + (d - oldSource G hG A c) = d := by abel
  rw [hs] at he
  change sourceWork G d d = sourceWork G (oldSource G hG A c) (oldSource G hG A c) +
    sourceWork G (d - oldSource G hG A c) (d - oldSource G hG A c) +
    2 * sourceWork G (oldSource G hG A c) (d - oldSource G hG A c) at he
  simpa only [ho, mul_zero, add_zero] using he

theorem record_lift_unique_minimum (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (c d : Fin N → ℝ) (hd : A *ᵥ d = A *ᵥ c) :
    sourceWork G (oldSource G hG A c) (oldSource G hG A c) ≤ sourceWork G d d ∧
      (sourceWork G d d = sourceWork G (oldSource G hG A c) (oldSource G hG A c) ↔
        d = oldSource G hG A c) := by
  have he := record_lift_pythagoras G hG A c d hd
  have hn := source_work_nonnegative G hG (d - oldSource G hG A c)
  constructor
  · linarith
  · constructor
    · intro heq
      have hz : sourceWork G (d - oldSource G hG A c) (d - oldSource G hG A c) = 0 := by
        linarith
      exact sub_eq_zero.mp ((source_work_zero_iff G hG _).mp hz)
    · intro heq
      rw [heq]

theorem entering_lift_unique_minimum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c d : Fin N → ℝ)
    (hd : enteringRecord G hG A B *ᵥ d = enteringRecord G hG A B *ᵥ c) :
    sourceWork G (enteringSource G hG A B c) (enteringSource G hG A B c) ≤ sourceWork G d d ∧
      (sourceWork G d d = sourceWork G (enteringSource G hG A B c) (enteringSource G hG A B c) ↔
        d = enteringSource G hG A B c) :=
  record_lift_unique_minimum G hG (enteringRecord G hG A B) c d hd

theorem actual_sampled_record_energy {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι (Fin (p - 1)) ℝ) (B : Matrix κ (Fin (p - 1)) ℝ) (c : Fin (p - 1) → ℝ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let E := enteringRecord G hG A B
    let u := oldSource G hG A c
    let v := enteringSource G hG A B c
    let z := residualSource G hG A B c
    sourceWork G c c = (A *ᵥ c) ⬝ᵥ (recordInverse G hG A *ᵥ (A *ᵥ c)) +
      (E *ᵥ c) ⬝ᵥ (recordInverse G hG E *ᵥ (E *ᵥ c)) + sourceWork G z z ∧
    sourceWork G u v = 0 ∧ sourceWork G u z = 0 ∧ sourceWork G v z = 0 ∧ A *ᵥ z = 0 ∧ B *ᵥ z = 0 := by
  dsimp only
  exact ⟨complete_record_energy _ _ A B c, old_entering_work_zero _ _ A B c,
    old_residual_work_zero _ _ A B c, entering_residual_work_zero _ _ A B c,
    residual_old_zero _ _ A B c, residual_later_zero _ _ A B c⟩

end NField.ResetForests.RecordGeometry
