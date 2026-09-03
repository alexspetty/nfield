/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRatioCompression

/-!
# Symmetric off-diagonal pairing

This module isolates the finite combinatorial step that pairs the two
orientations of every off-diagonal collision ratio.  It applies to any finite
linearly ordered window and any kernel invariant under inversion.
-/

namespace NField.Alignment.SymmetricOffDiagonalPairing

open scoped BigOperators
open NField.Alignment.CollisionRatioCompression

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
  [LinearOrder G]

/-- The strict upper-triangular part of a collision double sum. -/
noncomputable def collisionUpperTriangle
    (window : Finset G) (kernel : G → ℂ) : ℂ :=
  ∑ k ∈ window, ∑ u ∈ window with k < u, kernel (k⁻¹ * u)

omit [Fintype G] [DecidableEq G] in
/-- Swapping the two coordinates identifies the strict lower triangle with
the strict upper triangle when the kernel is invariant under inversion. -/
theorem collisionLowerTriangle_eq_upperTriangle
    (window : Finset G) (kernel : G → ℂ)
    (hinv : ∀ v : G, kernel v⁻¹ = kernel v) :
    (∑ k ∈ window, ∑ u ∈ window with u < k, kernel (k⁻¹ * u)) =
      collisionUpperTriangle window kernel := by
  classical
  unfold collisionUpperTriangle
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hku : k < u
  · have hnuk : ¬u < k := not_lt_of_ge (le_of_lt hku)
    simp [hnuk]
  · by_cases huk : u < k
    · simp only [huk, if_true]
      rw [show (k⁻¹ * u) = (u⁻¹ * k)⁻¹ by group, hinv]
    · simp [huk]

omit [Fintype G] in
/-- Every off-diagonal term occurs in exactly one strict triangle; inversion
symmetry makes the two triangles equal. -/
theorem collisionOffDiagonal_eq_two_mul_upperTriangle
    (window : Finset G) (kernel : G → ℂ)
    (hinv : ∀ v : G, kernel v⁻¹ = kernel v) :
    collisionOffDiagonal window kernel =
      2 * collisionUpperTriangle window kernel := by
  classical
  unfold collisionOffDiagonal
  have hsplit (k : G) :
      (∑ u ∈ window with u ≠ k, kernel (k⁻¹ * u)) =
        (∑ u ∈ window with u < k, kernel (k⁻¹ * u)) +
          ∑ u ∈ window with k < u, kernel (k⁻¹ * u) := by
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rcases lt_trichotomy u k with huk | rfl | hku
    · simp [huk, not_lt_of_ge (le_of_lt huk), ne_of_lt huk]
    · simp
    · simp [hku, not_lt_of_ge (le_of_lt hku), ne_of_gt hku]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [collisionLowerTriangle_eq_upperTriangle window kernel hinv]
  unfold collisionUpperTriangle
  ring

end NField.Alignment.SymmetricOffDiagonalPairing
