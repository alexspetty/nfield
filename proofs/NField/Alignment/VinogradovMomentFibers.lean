/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovAffine
import NField.Alignment.KaratsubaFiberEnergy

/-!
# Inhomogeneous integer moment fibers

The number of pairs with a prescribed difference of power-sum vectors is
at most the homogeneous moment count. The target group can be infinite;
all sums run over the finite image of the original tuple space. Mathlib's
finite Cauchy-Schwarz inequality supplies the estimate without reducing
the integer equations modulo an auxiliary modulus.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovMomentFibers
open scoped BigOperators Classical
open VinogradovDiagonal KaratsubaFiberEnergy

/-- Fiber populations vanish outside the actual finite image. -/
theorem fiberCount_eq_zero_of_not_mem_image {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) {y : β} (hy : y ∉ Finset.univ.image f) : fiberCount f y = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hy (Finset.mem_image.mpr
    ⟨x, Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)

/-- Cauchy-Schwarz for finite populations in an arbitrary additive group. -/
theorem finite_image_translation_correlation_le {α G : Type*} [Fintype α]
    [AddGroup G] [DecidableEq G] (f : α → G) (t : G) :
    (∑ y ∈ Finset.univ.image f, fiberCount f y * fiberCount f (y + t)) ≤
      ∑ y ∈ Finset.univ.image f, fiberCount f y ^ 2 := by
  let S := Finset.univ.image f
  have hshift : (∑ y ∈ S, fiberCount f (y + t) ^ 2) ≤
      ∑ y ∈ S, fiberCount f y ^ 2 := by
    calc
      _ = ∑ y ∈ S.image (fun z => z + t), fiberCount f y ^ 2 :=
        (Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_ne_zero
        intro y _ hy
        by_contra hmem
        exact hy (by rw [fiberCount_eq_zero_of_not_mem_image f hmem]; simp)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fiberCount f)
    (fun y => fiberCount f (y + t))
  have hsquare :
      (∑ y ∈ S, fiberCount f y * fiberCount f (y + t)) ^ 2 ≤
        (∑ y ∈ S, fiberCount f y ^ 2) ^ 2 := by
    calc
      _ ≤ _ := hcs
      _ ≤ (∑ y ∈ S, fiberCount f y ^ 2) * (∑ y ∈ S, fiberCount f y ^ 2) :=
        Nat.mul_le_mul_left _ hshift
      _ = _ := (pow_two _).symm
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hsquare

/-- A prescribed difference has no more ordered pairs than difference zero. -/
theorem shifted_pair_count_le {α G : Type*} [Fintype α] [AddGroup G] [DecidableEq G]
    (f : α → G) (t : G) :
    (Finset.univ.filter fun uv : α × α => f uv.2 = f uv.1 + t).card ≤
      (Finset.univ.filter fun uv : α × α => f uv.2 = f uv.1).card := by
  have hcount (a : G) :
      (Finset.univ.filter fun uv : α × α => f uv.2 = f uv.1 + a).card =
        ∑ y ∈ Finset.univ.image f, fiberCount f y * fiberCount f (y + a) := by
    calc
      _ = ∑ x : α, fiberCount f (f x + a) := by
        simp only [fiberCount, Finset.card_eq_sum_ones, Finset.sum_filter,
          Fintype.sum_prod_type]
      _ = _ := by
        simpa only [fiberCount, nsmul_eq_mul, Nat.cast_id] using
          (Finset.sum_comp (s := Finset.univ) (fun y => fiberCount f (y + a)) f)
  have hzero := hcount 0
  simp only [add_zero, ← pow_two] at hzero
  rw [hcount, hzero]
  exact finite_image_translation_correlation_le f t

/-- The integer vector of the first `k` power sums of an `s`-tuple. -/
def momentVector {S : Finset ℤ} {s : ℕ} (k : ℕ) (u : IntegerTuple S s) : Fin k → ℤ :=
  fun j => ∑ i, (u i).val ^ (j.val + 1)

/-- The actual number of ordered tuple pairs with a specified power-sum difference. -/
def shiftedMomentCount (S : Finset ℤ) (s k : ℕ) (a : Fin k → ℤ) : ℕ :=
  (Finset.univ.filter fun uv : IntegerTuple S s × IntegerTuple S s =>
    momentVector k uv.2 = momentVector k uv.1 + a).card

/-- The inhomogeneous integer system is bounded by the homogeneous Vinogradov count. -/
theorem shiftedMomentCount_le_momentCount (S : Finset ℤ) (s k : ℕ) (a : Fin k → ℤ) :
    shiftedMomentCount S s k a ≤ momentCount S s k := by
  rw [momentCount_eq_pair_count]
  simpa only [shiftedMomentCount, momentVector, funext_iff] using
    shifted_pair_count_le (momentVector (S := S) (s := s) k) a

end NField.Alignment.VinogradovMomentFibers
