/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RecordQuery
/-! # The literal sampled metric and arithmetic packet queries -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix

theorem image_inverse_left_on_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (y : ι → ℝ)
    (hy : y ∈ LinearMap.range H.mulVecLin) : imageInverse H hH *ᵥ (H *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← image_inverse_commute, ← Matrix.mulVec_mulVec]
  exact image_inverse_on_image H hH y hy

theorem actual_sampled_entering_rank {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι (Fin (p - 1)) ℝ) (B : Matrix κ (Fin (p - 1)) ℝ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    (enteringRecord G hG A B).rank = (Matrix.fromRows A B).rank - A.rank :=
  entering_record_rank_increase _ _ A B

theorem actual_sampled_lift_minima {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι (Fin (p - 1)) ℝ) (B : Matrix κ (Fin (p - 1)) ℝ)
    (c d e : Fin (p - 1) → ℝ) (hd : A *ᵥ d = A *ᵥ c) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let E := enteringRecord G hG A B
    let u := oldSource G hG A c
    let v := enteringSource G hG A B c
    E *ᵥ e = E *ᵥ c →
    (sourceWork G u u ≤ sourceWork G d d ∧ (sourceWork G d d = sourceWork G u u ↔ d = u)) ∧
    (sourceWork G v v ≤ sourceWork G e e ∧ (sourceWork G e e = sourceWork G v v ↔ e = v)) := by
  dsimp only
  intro he
  exact ⟨record_lift_unique_minimum _ _ A c d hd, entering_lift_unique_minimum _ _ A B c e he⟩

theorem actual_sampled_continuous_work {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι (Fin (p - 1)) ℝ) (B : Matrix κ (Fin (p - 1)) ℝ) (c : Fin (p - 1) → ℝ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let u := oldSource G hG A c
    let v := enteringSource G hG A B c
    let z := residualSource G hG A B c
    let I := fun x y => FibreReconstruction.continuousWork (p - 1)
      (SourceMetrics.cutoffCoefficients (p - 1) x) (SourceMetrics.cutoffCoefficients (p - 1) y)
    I c c = I u u + I v v + I z z + 2 * I u v + 2 * I u z + 2 * I v z :=
  complete_continuous_record_work _ _ A B c

theorem actual_packet_queries {p t0 t1 : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (κ0 : Fin t0 → ℕ) (κ1 : Fin t1 → ℕ) (c : Fin (p - 1) → ℝ) :
    let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
    let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
    let A := PacketQueries.packetRecord (p - 1) (p ^ 2) κ0
    let B := PacketQueries.packetRecord (p - 1) (p ^ 2) κ1
    let T := laterPrediction G hG A B
    let E := enteringRecord G hG A B
    PacketQueries.packetQuery (p - 1) (p ^ 2) κ0 c + PacketQueries.packetQuery (p - 1) (p ^ 2) κ1 c =
      blockReading (PacketQueries.pairQuery t0 + Tᵀ * PacketQueries.pairQuery t1 * T)
        (Tᵀ * PacketQueries.pairQuery t1) (PacketQueries.pairQuery t1) (A *ᵥ c) (E *ᵥ c) := by
  dsimp only
  rw [PacketQueries.packet_record_quadratic, PacketQueries.packet_record_quadratic,
    PacketQueries.pullback_query_quadratic, PacketQueries.pullback_query_quadratic]
  apply complete_record_query
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    PacketQueries.pair_query_symmetric t1

end NField.ResetForests.RecordGeometry
