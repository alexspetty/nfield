/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.CovectorProjection
/-! # Coarsening actual source increments and comparison with Mathlib projections -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix InnerProductSpace
open RecordGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prefix_block_sum (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (a n : ℕ) :
    (∑ i ∈ Finset.range n, prefixIncrement G hG A J c (a + i)) =
      prefixSource G hG A J c (a + n) - prefixSource G hG A J c a := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [prefixIncrement, Nat.add_assoc]
    abel

theorem grouped_metric_cost_le (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (s : Finset ℕ) (v : ℕ → Fin N → ℝ) (f : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0)
    (groups : Finset (Finset ℕ))
    (hdisj : (groups : Set (Finset ℕ)).PairwiseDisjoint id) (hcover : groups.biUnion id = s) :
    (∑ B ∈ groups, (f (∑ i ∈ B, v i)) ^ 2 /
      sourceWork G (∑ i ∈ B, v i) (∑ i ∈ B, v i)) ≤
      Core.readoutCost s (fun i => sourceWork G (v i) (v i)) (fun i => f (v i)) := by
  have hsub {B : Finset ℕ} (hB : B ∈ groups) : B ⊆ s := by
    intro i hi
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨B, hB, hi⟩
  calc
    _ ≤ ∑ B ∈ groups, Core.readoutCost B (fun i => sourceWork G (v i) (v i))
        (fun i => f (v i)) := by
      apply Finset.sum_le_sum
      intro B hB
      rw [map_sum, orthogonal_source_work G B v
        (by intro i hi j hj hij; exact ho i (hsub hB hi) j (hsub hB hj) hij)]
      exact Core.coarsened_readout_cost_le B _ _
        (fun i _ => source_work_nonnegative G hG (v i))
        (by intro i _ hi; rw [(source_work_zero_iff G hG _).mp hi, map_zero])
    _ = _ := by
      unfold Core.readoutCost
      have hs := Finset.sum_biUnion (f := fun i => (f (v i)) ^ 2 / sourceWork G (v i) (v i)) hdisj
      simpa only [hcover, id_eq] using hs.symm

theorem prefix_coarsening_cost_le (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (L : ℕ) (groups : Finset (Finset ℕ))
    (hdisj : (groups : Set (Finset ℕ)).PairwiseDisjoint id)
    (hcover : groups.biUnion id = Finset.range L) :
    (∑ B ∈ groups, (finalReadout A b (∑ i ∈ B, prefixIncrement G hG A J c i)) ^ 2 /
      sourceWork G (∑ i ∈ B, prefixIncrement G hG A J c i)
        (∑ i ∈ B, prefixIncrement G hG A J c i)) ≤ prefixCost G hG A b J c L :=
  grouped_metric_cost_le G hG (Finset.range L) (prefixIncrement G hG A J c) (finalReadout A b)
    (by intro i _ j _ hij; exact prefix_increments_orthogonal G hG A J hJ c hij)
    groups hdisj hcover

@[implicit_reducible]
def sourceInnerProductSpace (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    letI := G.toNormedAddCommGroup hG
    letI : SeminormedAddCommGroup (Fin N → ℝ) := (G.toNormedAddCommGroup hG).toSeminormedAddCommGroup
    InnerProductSpace ℝ (Fin N → ℝ) := by
  letI := G.toNormedAddCommGroup hG
  letI : SeminormedAddCommGroup (Fin N → ℝ) := (G.toNormedAddCommGroup hG).toSeminormedAddCommGroup
  let H := G.toInnerProductSpace hG.posSemidef
  exact {
    toModule := inferInstance
    norm_smul_le := H.norm_smul_le
    inner := H.inner
    norm_sq_eq_re_inner := H.norm_sq_eq_re_inner
    conj_inner_symm := H.conj_inner_symm
    add_left := H.add_left
    smul_left := H.smul_left }

/-- The matrix work is literally the squared norm in Mathlib's metric
induced by this positive matrix, with no rescaling of the source. -/
theorem source_metric_norm_sq (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) (x : Fin N → ℝ) :
    (@norm (Fin N → ℝ) (G.toNormedAddCommGroup hG).toSeminormedAddCommGroup.toNorm x) ^ 2 =
      sourceWork G x x := by
  change (Real.sqrt ((G *ᵥ x) ⬝ᵥ x)) ^ 2 = x ⬝ᵥ (G *ᵥ x)
  rw [Real.sq_sqrt (by simpa only [sourceWork, dotProduct_comm] using source_work_nonnegative G hG x)]
  exact dotProduct_comm _ _

end NField.ResetForests.PrefixGeometry
