/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlockGrowth
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# A grid for bounded partial-sum paths

The one-based widths are exactly 1/j². Their total is at most two.
Half-open grid cells partition the finite vector space; any cell meeting
a path event is contained in the path event with both boundaries expanded
by two. This is a deterministic statement, before probability transfer.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPathGrid
open scoped BigOperators
open Set

def width {n : ℕ} (i : Fin n) : ℝ := 1/((i.val : ℝ)+1)^2

def partialSum {n : ℕ} (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.Iic j, z i

def pathEvent {n : ℕ} (u v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | ∀ j, u j ≤ partialSum z j ∧ partialSum z j ≤ v j}

def gridStart {n : ℕ} (k : Fin n → ℤ) (i : Fin n) : ℝ := (k i : ℝ)*width i

def gridCell {n : ℕ} (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Ico (gridStart k i) (gridStart k i+width i))

def closedGridCell {n : ℕ} (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Icc (gridStart k i) (gridStart k i+width i))

def selectedCells {n : ℕ} (u v : Fin n → ℝ) : Set (Fin n → ℤ) :=
  {k | (gridCell k ∩ pathEvent u v).Nonempty}

theorem width_pos {n : ℕ} (i : Fin n) : 0 < width i := by
  unfold width
  positivity

theorem width_le_one {n : ℕ} (i : Fin n) : width i ≤ 1 := by
  unfold width
  exact HarperPrimeBlockGrowth.reciprocal_square_width_le_one
    (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)

theorem sum_width_le_two (n : ℕ) : (∑ i : Fin n, width i) ≤ 2 := by
  have he : (∑ i : Fin n, width i) =
      ∑ j ∈ Finset.Ioo 0 (n+1), ((j : ℝ)^2)⁻¹ := by
    refine Finset.sum_bij (fun i _ => i.val+1) ?_ ?_ ?_ ?_
    · intro i _
      simp only [Finset.mem_Ioo]
      omega
    · intro a _ b _ hab
      exact Fin.ext (by omega)
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      refine ⟨⟨j-1,by omega⟩,Finset.mem_univ _,?_⟩
      dsimp
      omega
    · intro i _
      simp [width]
  rw [he]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (n+1))

theorem partial_width_le_two {n : ℕ} (j : Fin n) : partialSum width j ≤ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => (width_pos i).le)).trans (sum_width_le_two n)

theorem mem_gridCell_iff {n : ℕ} (k : Fin n → ℤ) (z : Fin n → ℝ) :
    z ∈ gridCell k ↔ ∀ i, gridStart k i ≤ z i ∧ z i < gridStart k i+width i := by
  simp [gridCell]

theorem mem_closedGridCell_iff {n : ℕ} (k : Fin n → ℤ) (z : Fin n → ℝ) :
    z ∈ closedGridCell k ↔ ∀ i, gridStart k i ≤ z i ∧ z i ≤ gridStart k i+width i := by
  simp only [closedGridCell, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

theorem gridCell_subset_closedGridCell {n : ℕ} (k : Fin n → ℤ) :
    gridCell k ⊆ closedGridCell k := by
  intro z hz
  exact (mem_closedGridCell_iff k z).mpr
    (fun i => ⟨((mem_gridCell_iff k z).mp hz i).1,((mem_gridCell_iff k z).mp hz i).2.le⟩)

theorem exists_gridCell {n : ℕ} (z : Fin n → ℝ) : ∃ k, z ∈ gridCell k := by
  refine ⟨fun i => ⌊z i/width i⌋, (mem_gridCell_iff _ _).mpr fun i => ?_⟩
  have hlo := (le_div_iff₀ (width_pos i)).mp (Int.floor_le (z i/width i))
  have hhi := (div_lt_iff₀ (width_pos i)).mp (Int.lt_floor_add_one (z i/width i))
  exact ⟨hlo,by simpa [gridStart, add_mul] using hhi⟩

theorem gridCell_pairwise_disjoint (n : ℕ) :
    Pairwise (fun k l : Fin n → ℤ => Disjoint (gridCell k) (gridCell l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hk hl
  apply hkl
  funext i
  have hk := (mem_gridCell_iff k z).mp hk i
  have hl := (mem_gridCell_iff l z).mp hl i
  have hki : (k i : ℝ) ≤ z i/width i := (le_div_iff₀ (width_pos i)).mpr hk.1
  have hli : (l i : ℝ) ≤ z i/width i := (le_div_iff₀ (width_pos i)).mpr hl.1
  have hki' : z i/width i < (k i : ℝ)+1 :=
    (div_lt_iff₀ (width_pos i)).mpr (by simpa [gridStart,add_mul] using hk.2)
  have hli' : z i/width i < (l i : ℝ)+1 :=
    (div_lt_iff₀ (width_pos i)).mpr (by simpa [gridStart,add_mul] using hl.2)
  have heqk : ⌊z i/width i⌋ = k i := Int.floor_eq_iff.mpr ⟨hki,hki'⟩
  have heql : ⌊z i/width i⌋ = l i := Int.floor_eq_iff.mpr ⟨hli,hli'⟩
  exact heqk.symm.trans heql

theorem partialSum_sub_abs_le_two {n : ℕ} {k : Fin n → ℤ}
    {z y : Fin n → ℝ} (hz : z ∈ closedGridCell k) (hy : y ∈ closedGridCell k)
    (j : Fin n) : |partialSum z j-partialSum y j| ≤ 2 := by
  have hi (i : Fin n) : |z i-y i| ≤ width i := by
    have hz := (mem_closedGridCell_iff k z).mp hz i
    have hy := (mem_closedGridCell_iff k y).mp hy i
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ = |∑ i ∈ Finset.Iic j, (z i-y i)| := by rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i ∈ Finset.Iic j, |z i-y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ partialSum width j := Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ 2 := partial_width_le_two j

theorem selected_cell_subset_expanded_path {n : ℕ} {u v : Fin n → ℝ}
    {k : Fin n → ℤ} (hk : k ∈ selectedCells u v) :
    closedGridCell k ⊆ pathEvent (fun j => u j-2) (fun j => v j+2) := by
  rcases hk with ⟨y,hy,hyp⟩
  intro z hz j
  have h := abs_le.mp (partialSum_sub_abs_le_two hz (gridCell_subset_closedGridCell k hy) j)
  have hp := hyp j
  exact ⟨by linarith,by linarith⟩

theorem path_subset_selected_union {n : ℕ} (u v : Fin n → ℝ) :
    pathEvent u v ⊆ ⋃ k : selectedCells u v, gridCell k.val := by
  intro z hz
  obtain ⟨k,hk⟩ := exists_gridCell z
  exact Set.mem_iUnion.mpr ⟨⟨k,⟨z,hk,hz⟩⟩,hk⟩

theorem coordinate_abs_le_of_partialSum {n : ℕ} {z R : Fin n → ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : Monotone R)
    (hz : ∀ j, |partialSum z j| ≤ R j) (j : Fin n) : |z j| ≤ 2*R j := by
  have hprev : |∑ i ∈ Finset.Iio j, z i| ≤ R j := by
    by_cases hj : j.val = 0
    · have he : Finset.Iio j = ∅ := by
        ext i
        simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false]
        exact not_lt.mpr (show j ≤ i by simp [Fin.le_def,hj])
      simpa [he] using hR0 j
    · let p : Fin n := ⟨j.val-1,by omega⟩
      have he : Finset.Iio j = Finset.Iic p := by
        ext i
        simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_def]
        dsimp [p]
        omega
      rw [he]
      exact (hz p).trans (hR (show p ≤ j by simp [p,Fin.le_def]))
  have he := Finset.sum_Iio_add_eq_sum_Iic (f := z) j
  have hp := abs_le.mp (hz j)
  have hq := abs_le.mp hprev
  change (∑ i ∈ Finset.Iio j, z i)+z j = partialSum z j at he
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem selected_gridStart_abs_le {n : ℕ} {u v R : Fin n → ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : Monotone R)
    (hu : ∀ i, -R i ≤ u i) (hv : ∀ i, v i ≤ R i)
    {k : Fin n → ℤ} (hk : k ∈ selectedCells u v) (i : Fin n) :
    |gridStart k i| ≤ 2*R i+1 := by
  rcases hk with ⟨z,hz,hp⟩
  have hp' : ∀ j, |partialSum z j| ≤ R j := fun j =>
    abs_le.mpr ⟨(hu j).trans (hp j).1,((hp j).2).trans (hv j)⟩
  have hi := abs_le.mp (coordinate_abs_le_of_partialSum hR0 hR hp' i)
  have hc := (mem_gridCell_iff k z).mp hz i
  have hw := width_le_one i
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NField.Alignment.HarperPathGrid
