/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixProjection
/-! # Source increments of a fixed nested physical-prefix partition -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def prefixSource (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    Fin N → ℝ := oldSource G hG (restrictedRecord A (J r)) c

def prefixIncrement (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    Fin N → ℝ := prefixSource G hG A J c (r + 1) - prefixSource G hG A J c r

theorem prefix_zero (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (h0 : J 0 = ∅) (c : Fin N → ℝ) :
    prefixSource G hG A J c 0 = 0 := by
  unfold prefixSource
  rw [h0, empty_projection]

theorem prefix_increment_kernel (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) {i r : ℕ} (hir : i ≤ r) :
    restrictedRecord A (J i) *ᵥ prefixIncrement G hG A J c r = 0 := by
  unfold prefixIncrement prefixSource
  rw [Matrix.mulVec_sub, restricted_nested_readback G hG A (hJ (by omega)) c,
    restricted_nested_readback G hG A (hJ hir) c, sub_self]

theorem prefix_source_increment_work (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) {i r : ℕ} (hir : i ≤ r) :
    sourceWork G (prefixSource G hG A J c i) (prefixIncrement G hG A J c r) = 0 :=
  lifted_kernel_work_zero G hG (restrictedRecord A (J i)) _ _
    (prefix_increment_kernel G hG A J hJ c hir)

theorem prefix_increments_orthogonal (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) {i j : ℕ} (hij : i ≠ j) :
    sourceWork G (prefixIncrement G hG A J c i) (prefixIncrement G hG A J c j) = 0 := by
  have hlt {i j : ℕ} (h : i < j) :
      sourceWork G (prefixIncrement G hG A J c i) (prefixIncrement G hG A J c j) = 0 := by
    unfold prefixIncrement
    rw [work_sub_left]
    change sourceWork G (prefixSource G hG A J c (i + 1))
        (prefixIncrement G hG A J c j) -
      sourceWork G (prefixSource G hG A J c i) (prefixIncrement G hG A J c j) = 0
    rw [prefix_source_increment_work G hG A J hJ c (by omega),
      prefix_source_increment_work G hG A J hJ c (by omega), sub_self]
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt h
  · rw [work_symm G hG.1]
    exact hlt h

theorem prefix_increment_sum (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (h0 : J 0 = ∅)
    (c : Fin N → ℝ) (L : ℕ) :
    (∑ r ∈ Finset.range L, prefixIncrement G hG A J c r) = prefixSource G hG A J c L := by
  induction L with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, prefix_zero G hG A J h0 c]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    unfold prefixIncrement
    abel

theorem orthogonal_source_work {κ : Type*} (G : Matrix (Fin N) (Fin N) ℝ)
    (s : Finset κ) (v : κ → Fin N → ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sourceWork G (v i) (v j) = 0) :
    sourceWork G (∑ i ∈ s, v i) (∑ i ∈ s, v i) = ∑ i ∈ s, sourceWork G (v i) (v i) := by
  classical
  rw [work_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [work_sum_right]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact ho i hi j hj (Ne.symm hji)
  · exact fun h => (h hi).elim

theorem prefix_increment_energy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (r : ℕ) :
    sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) =
      sourceWork G (prefixSource G hG A J c (r + 1)) (prefixSource G hG A J c (r + 1)) -
        sourceWork G (prefixSource G hG A J c r) (prefixSource G hG A J c r) := by
  have he := record_lift_pythagoras G hG (restrictedRecord A (J r)) c
    (prefixSource G hG A J c (r + 1))
    (restricted_nested_readback G hG A (hJ (by omega : r ≤ r + 1)) c)
  change sourceWork G (prefixSource G hG A J c (r + 1)) (prefixSource G hG A J c (r + 1)) =
    sourceWork G (prefixSource G hG A J c r) (prefixSource G hG A J c r) +
      sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r) at he
  linarith

theorem prefix_complete_source_energy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (hJ : Monotone J) (h0 : J 0 = ∅)
    (c : Fin N → ℝ) (L : ℕ) :
    (∑ r ∈ Finset.range L, sourceWork G (prefixIncrement G hG A J c r)
        (prefixIncrement G hG A J c r)) +
      sourceWork G (c - prefixSource G hG A J c L) (c - prefixSource G hG A J c L) =
        sourceWork G c c := by
  have hs := orthogonal_source_work G (Finset.range L) (prefixIncrement G hG A J c)
    (by intro i _ j _ hij; exact prefix_increments_orthogonal G hG A J hJ c hij)
  rw [prefix_increment_sum G hG A J h0 c L] at hs
  have he := record_lift_pythagoras G hG (restrictedRecord A (J L)) c c rfl
  change sourceWork G c c = sourceWork G (prefixSource G hG A J c L)
    (prefixSource G hG A J c L) +
    sourceWork G (c - prefixSource G hG A J c L) (c - prefixSource G hG A J c L) at he
  rw [hs] at he
  exact he.symm

theorem prefix_work_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    sourceWork G (prefixSource G hG A J c r) (prefixSource G hG A J c r) =
      (restrictedRecord A (J r) *ᵥ c) ⬝ᵥ
        (recordInverse G hG (restrictedRecord A (J r)) *ᵥ (restrictedRecord A (J r) *ᵥ c)) :=
  lifted_record_work G hG (restrictedRecord A (J r)) c

end NField.ResetForests.PrefixGeometry
