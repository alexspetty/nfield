/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindCollisionKernel

/-!
# Collision-ratio compression

This module proves the weight-removal step independently of any analytic
estimate.  A collision weight counts first-window pairs with a fixed ratio;
finite reindexing turns its weighted sum into the exact double sum over the two
window coordinates.  The diagonal is then isolated without approximation.
-/

namespace NField.Alignment.CollisionRatioCompression

open scoped BigOperators

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Number of window coordinates `k` for which multiplication by `v` remains
inside the same window. -/
def collisionRatioWeight (window : Finset G) (v : G) : ℕ :=
  (window.filter fun k => k * v ∈ window).card

/-- The weighted ratio sum. -/
noncomputable def weightedRatioSum
    (window : Finset G) (kernel : G → ℂ) : ℂ :=
  ∑ v : G, (collisionRatioWeight window v : ℂ) * kernel v

/-- The weight-free double sum over the two collision-window coordinates. -/
noncomputable def collisionDoubleSum
    (window : Finset G) (kernel : G → ℂ) : ℂ :=
  ∑ k ∈ window, ∑ u ∈ window, kernel (k⁻¹ * u)

omit [Fintype G] in
/-- The collision weight is its literal indicator sum. -/
theorem collisionRatioWeight_cast
    (window : Finset G) (v : G) :
    (collisionRatioWeight window v : ℂ) =
      ∑ k ∈ window, if k * v ∈ window then 1 else 0 := by
  classical
  unfold collisionRatioWeight
  rw [Finset.card_filter]
  push_cast
  rfl

/-- For a fixed left coordinate, multiplying the ratio by that coordinate
reindexes the group sum onto the right window. -/
theorem fixedCoordinate_reindex
    (window : Finset G) (kernel : G → ℂ) (k : G) :
    (∑ v : G, (if k * v ∈ window then 1 else 0) * kernel v) =
      ∑ u ∈ window, kernel (k⁻¹ * u) := by
  classical
  let e : G ≃ G := Equiv.mulLeft k
  let f : G → ℂ := fun u =>
    (if u ∈ window then 1 else 0) * kernel (k⁻¹ * u)
  have hreindex : (∑ v : G, f (e v)) = ∑ u : G, f u :=
    e.sum_comp f
  have hleft : (∑ v : G, f (e v)) =
      ∑ v : G, (if k * v ∈ window then 1 else 0) * kernel v := by
    apply Finset.sum_congr rfl
    intro v _
    dsimp [f, e]
    simp
  have hright : (∑ u : G, f u) =
      ∑ u ∈ window, kernel (k⁻¹ * u) := by
    unfold f
    simp
  rw [← hleft, hreindex, hright]

/-- Exact removal of the collision weight. -/
theorem weightedRatioSum_eq_collisionDoubleSum
    (window : Finset G) (kernel : G → ℂ) :
    weightedRatioSum window kernel = collisionDoubleSum window kernel := by
  classical
  unfold weightedRatioSum collisionDoubleSum
  simp_rw [collisionRatioWeight_cast]
  calc
    (∑ v : G,
        (∑ k ∈ window, if k * v ∈ window then 1 else 0) * kernel v) =
      ∑ v : G, ∑ k ∈ window,
        (if k * v ∈ window then 1 else 0) * kernel v := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.sum_mul]
    _ = ∑ k ∈ window, ∑ v : G,
        (if k * v ∈ window then 1 else 0) * kernel v := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ window, ∑ u ∈ window,
        kernel (k⁻¹ * u) := by
          apply Finset.sum_congr rfl
          intro k _
          exact fixedCoordinate_reindex window kernel k

/-- Off-diagonal part of the collision double sum. -/
noncomputable def collisionOffDiagonal
    (window : Finset G) (kernel : G → ℂ) : ℂ :=
  ∑ k ∈ window, ∑ u ∈ window with u ≠ k, kernel (k⁻¹ * u)

omit [Fintype G] in
/-- The diagonal is exactly one copy of `kernel 1` for each window element. -/
theorem collisionDoubleSum_diagonal_offDiagonal
    (window : Finset G) (kernel : G → ℂ) :
    collisionDoubleSum window kernel =
      (window.card : ℂ) * kernel 1 +
        collisionOffDiagonal window kernel := by
  classical
  unfold collisionDoubleSum collisionOffDiagonal
  calc
    (∑ k ∈ window, ∑ u ∈ window, kernel (k⁻¹ * u)) =
      ∑ k ∈ window,
        (kernel (k⁻¹ * k) +
          ∑ u ∈ window with u ≠ k, kernel (k⁻¹ * u)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.add_sum_erase _ _ hk]
            congr 1
            rw [show window.erase k = window.filter (fun u => u ≠ k) by
              ext u
              simp [and_comm]]
    _ = ∑ k ∈ window,
        (kernel 1 +
          ∑ u ∈ window with u ≠ k, kernel (k⁻¹ * u)) := by
            apply Finset.sum_congr rfl
            intro k _
            simp
    _ = (window.card : ℂ) * kernel 1 +
        ∑ k ∈ window,
          ∑ u ∈ window with u ≠ k, kernel (k⁻¹ * u) := by
            rw [Finset.sum_add_distrib]
            simp

end NField.Alignment.CollisionRatioCompression
