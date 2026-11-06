/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevBlockResidualRange

/-! # Residual population cost for bounded-ratio prime blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevBlockResidualVolume
open KorolevCanonicalPrimeSlices KorolevLogarithmicPartition KorolevBlockResidualRange
open scoped BigOperators Classical

/-- A set of positive integers below a real endpoint has at most that endpoint's population. -/
theorem card_le_upper {S : Finset ℕ} {U : ℝ} (hU : 0 ≤ U)
    (hpos : ∀ n ∈ S, 1 ≤ n) (hupper : ∀ n ∈ S, (n : ℝ) ≤ U) :
    (S.card : ℝ) ≤ U := by
  have hs : S ⊆ Finset.Icc 1 ⌊U⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨hpos n hn, Nat.le_floor (hupper n hn)⟩
  have hc : S.card ≤ ⌊U⌋₊ := by simpa using Finset.card_le_card hs
  exact (show (S.card : ℝ) ≤ ⌊U⌋₊ by exact_mod_cast hc).trans (Nat.floor_le hU)

/-- Actual prime-block populations are bounded by their upper endpoints. -/
theorem block_card_le_upper (l D A : ℝ) (i : ℕ) :
    ((block l D A i).card : ℝ) ≤ point l D A (i+1) := by
  apply card_le_upper (Real.exp_pos _).le
  · intro p hp
    exact (KorolevPrimeIntervals.intervalPrimes_mem.mp hp).1.pos
  · intro p hp
    exact (KorolevPrimeIntervals.intervalPrimes_mem.mp hp).2.2

/-- The residual count cancels the block's endpoint populations at a fixed ratio cost. -/
theorem residual_population_cost (l X : ℕ) (hl : 0 < l) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq) (i j : ℕ) :
    ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ) *
      (residualBound l X (point lp Dp A i) (point lq Dq A j) : ℝ) ≤
        Real.exp (4*A) * (X : ℝ) / (l : ℝ)^2 := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hu : 0 < point lp Dp A i := Real.exp_pos _
  have hv : 0 < point lq Dq A j := Real.exp_pos _
  have hp := (block_card_le_upper lp Dp A i).trans (point_ratio_bound lp hA hDp i)
  have hq := (block_card_le_upper lq Dq A j).trans (point_ratio_bound lq hA hDq j)
  have hr := residualBound_le_ratio l X hu.le hv.le
  calc
    _ ≤ (point lp Dp A i * Real.exp (2*A)) *
        (point lq Dq A j * Real.exp (2*A)) *
        ((X : ℝ)/((l : ℝ)^2*point lp Dp A i*point lq Dq A j)) := by
      apply mul_le_mul (mul_le_mul hp hq (by positivity) (by positivity)) hr
        (by positivity) (by positivity)
    _ = Real.exp (4*A) * (X : ℝ) / (l : ℝ)^2 := by
      rw [show 4*A = 2*A+2*A by ring, Real.exp_add]
      field_simp [ne_of_gt hlR, ne_of_gt hu, ne_of_gt hv]

/-- A uniform normalized bound on the surviving slices sums at the residual population cost. -/
theorem norm_residual_sum_le (P Q : Finset ℕ) (l X m : ℕ) (hl : 0 < l)
    (f : ℕ → ℂ) (lp lq : ℝ) {Dp Dq A δ : ℝ}
    (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq) (hδ : 0 ≤ δ) (i j : ℕ)
    (hslice : ∀ h ∈ (Finset.Icc 1 (residualBound l X (point lp Dp A i) (point lq Dq A j))).filter
      (fun h => Squarefree h ∧ h.Coprime m),
      ‖primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f‖ ≤
        δ * ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ)) :
    ‖∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
      primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f‖ ≤
        δ * (Real.exp (4*A) * (X : ℝ) / (l : ℝ)^2) := by
  rw [sum_block_residual_truncated P Q l X m f lp lq Dp Dq A i j hl]
  let H := residualBound l X (point lp Dp A i) (point lq Dq A j)
  let S := (Finset.Icc 1 H).filter (fun h => Squarefree h ∧ h.Coprime m)
  have hcard : (S.card : ℝ) ≤ H := by
    exact_mod_cast (show S.card ≤ H by simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.Icc 1 H)))
  have hb : 0 ≤ δ * ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ) := by positivity
  calc
    _ ≤ ∑ h ∈ S, ‖primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ S, δ * ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ) :=
      Finset.sum_le_sum hslice
    _ = (S.card : ℝ) * (δ * ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ)) := by simp
    _ ≤ (H : ℝ) * (δ * ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hb
    _ = δ * (((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ) * H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (residual_population_cost l X hl lp lq hA hDp hDq i j) hδ

end NField.Alignment.KorolevBlockResidualVolume
