/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactProjection
/-! # Linear witnesses retain every physical row in the actual prefix -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open PacketQueries RecordGeometry PrefixGeometry

def clockRow (p k : ℕ) (b : Bool) : Fin (p - 1) → ℝ :=
  if b then detectorRow (p - 1) (p ^ 2) k else resetRow (p - 1) k

def rationalClockRow (p k : ℕ) (b : Bool) (j : Fin (p - 1)) : ℚ :=
  if b then exactDetector (p ^ 2) k (j.val + 1) else if k ∣ j.val + 1 then 1 else 0

theorem clock_row_exact (p : ℕ) {k : ℕ} (hk : 0 < k) (b : Bool) :
    clockRow p k b = castVector (rationalClockRow p k b) := by
  funext j
  cases b
  · by_cases h : k ∣ j.val + 1 <;>
      simp [clockRow, rationalClockRow, resetRow, castVector, h]
  · exact detector_row_exact hk j

theorem prefix_clocks_subset (p : ℕ) (loads : Finset ℕ) (n : ℕ) :
    prefixClocks p loads n ⊆ chosenClocks p loads := by
  intro k hk
  obtain ⟨a, ha, hk⟩ := Finset.mem_biUnion.mp hk
  have hmem : a ∈ orderedPackets p loads := List.mem_of_mem_take (List.mem_toFinset.mp ha)
  have hkey : a ∈ packetKeys p loads := by simpa only [orderedPackets, Finset.mem_sort] using hmem
  exact Finset.mem_biUnion.mpr ⟨a, hkey, hk⟩

theorem prefix_transpose_witness (p : ℕ) (loads : Finset ℕ) (cuts : ℕ → ℕ) (r : ℕ)
    (w : ℕ → Bool → ℝ) :
    (restrictedRecord (physicalRecord p loads) (physicalPrefixes p loads cuts r))ᵀ *ᵥ
        (fun i => w i.1.val i.2) =
      fun j => ∑ k ∈ prefixClocks p loads (cuts r),
        (clockRow p k false j * w k false + clockRow p k true j * w k true) := by
  let S := prefixClocks p loads (cuts r)
  have hs : (chosenClocks p loads).filter (fun k => k ∈ S) = S := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨prefix_clocks_subset p loads (cuts r) h, h⟩⟩
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, restrictedRecord, physicalPrefixes,
    Finset.mem_filter, Finset.mem_univ, true_and, physicalRecord,
    Bool.false_eq_true, if_false, if_true]
  change (∑ k : ↥(chosenClocks p loads),
      ((if k.val ∈ S then detectorRow (p - 1) (p ^ 2) k.val j else 0) * w k.val true +
       (if k.val ∈ S then resetRow (p - 1) k.val j else 0) * w k.val false)) = _
  rw [Finset.sum_coe_sort (chosenClocks p loads) (fun k : ℕ =>
      ((if k ∈ S then detectorRow (p - 1) (p ^ 2) k j else 0) * w k true +
       (if k ∈ S then resetRow (p - 1) k j else 0) * w k false))]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [hs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [clockRow, Bool.false_eq_true, if_false, if_true]
  ring

theorem actual_prefix_from_linear_witness (p : ℕ) (loads : Finset ℕ)
    (cuts : ℕ → ℕ) (r : ℕ)
    (G : Matrix (Fin (p - 1)) (Fin (p - 1)) ℝ) (hG : G.PosDef)
    (c z : Fin (p - 1) → ℝ) (w : ℕ → Bool → ℝ)
    (hz : G *ᵥ z = fun j => ∑ k ∈ prefixClocks p loads (cuts r),
      (clockRow p k false j * w k false + clockRow p k true j * w k true))
    (hc : ∀ k ∈ prefixClocks p loads (cuts r), ∀ b,
      clockRow p k b ⬝ᵥ z = clockRow p k b ⬝ᵥ c) :
    prefixSource G hG (physicalRecord p loads) (physicalPrefixes p loads cuts) c r = z := by
  apply projection_from_linear_witness _ _ _ _ _ (fun i => w i.1.val i.2)
  · rw [prefix_transpose_witness]
    exact hz
  · ext i
    rw [restricted_reading, restricted_reading]
    by_cases hi : i.1.val ∈ prefixClocks p loads (cuts r)
    · simp only [physicalPrefixes, Finset.mem_filter, Finset.mem_univ,
        true_and, hi, if_true]
      cases hb : i.2 <;>
        simpa only [Matrix.mulVec, physicalRecord, clockRow, hb,
          Bool.false_eq_true, if_false, if_true] using hc i.1.val hi i.2
    · simp only [physicalPrefixes, Finset.mem_filter, Finset.mem_univ,
        true_and, hi, if_false]

theorem rational_actual_prefix_witness {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (loads : Finset ℕ) (cuts : ℕ → ℕ) (r : ℕ)
    (c z : Fin (p - 1) → ℚ) (w : ℕ → Bool → ℚ)
    (hpos : ∀ k ∈ prefixClocks p loads (cuts r), 0 < k)
    (hz : exactGram (p - 1) (p ^ 2) *ᵥ z =
      fun j => ∑ k ∈ prefixClocks p loads (cuts r),
        (rationalClockRow p k false j * w k false + rationalClockRow p k true j * w k true))
    (hc : ∀ k ∈ prefixClocks p loads (cuts r), ∀ b,
      rationalClockRow p k b ⬝ᵥ z = rationalClockRow p k b ⬝ᵥ c) :
    prefixSource (SourceMetrics.sampledGram (p - 1) (p ^ 2))
      (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
      (physicalRecord p loads) (physicalPrefixes p loads cuts) (castVector c) r = castVector z := by
  apply actual_prefix_from_linear_witness _ _ _ _ _ _ _ _ (fun k b => (w k b : ℝ))
  · rw [sampled_gram_exact (pow_pos hp.pos 2), ← cast_vector_mulVec, hz]
    funext j
    change ((∑ k ∈ prefixClocks p loads (cuts r),
      (rationalClockRow p k false j * w k false + rationalClockRow p k true j * w k true) : ℚ) : ℝ) = _
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [clock_row_exact p (hpos k hk) false, clock_row_exact p (hpos k hk) true]
    rfl
  · intro k hk b
    rw [clock_row_exact p (hpos k hk) b]
    change (∑ j, (rationalClockRow p k b j : ℝ) * (z j : ℝ)) =
      ∑ j, (rationalClockRow p k b j : ℝ) * (c j : ℝ)
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hc k hk b)
    change ((∑ j, rationalClockRow p k b j * z j : ℚ) : ℝ) =
      ((∑ j, rationalClockRow p k b j * c j : ℚ) : ℝ) at h
    push_cast at h
    exact h

def rationalReadout (p : ℕ) (C : Finset ℕ) (z : Fin (p - 1) → ℚ) : ℚ :=
  ∑ k ∈ C, 4 * ((p - 1) / k : ℕ) * (rationalClockRow p k true ⬝ᵥ z)

theorem physical_readout_rational (p : ℕ) (loads : Finset ℕ)
    (hpos : ∀ k ∈ chosenClocks p loads, 0 < k) (c : Fin (p - 1) → ℚ) :
    finalReadout (physicalRecord p loads) (physicalReadoutWeights p loads) (castVector c) =
      (rationalReadout p (chosenClocks p loads) c : ℝ) := by
  rw [physical_linear_readout]
  unfold rationalReadout
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  change 4 * (((p - 1) / k : ℕ) : ℝ) * (clockRow p k true ⬝ᵥ castVector c) = _
  rw [clock_row_exact p (hpos k hk) true]
  congr 1
  exact ((Rat.castHom ℝ).map_dotProduct (rationalClockRow p k true) c).symm

end NField.ResetForests.ExactCost
