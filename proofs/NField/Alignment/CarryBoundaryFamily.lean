/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-! # The exact kernel for a selected family of ordinary boundary fluxes -/

noncomputable section
namespace NField.Alignment.CarryBoundaryFamily
open scoped BigOperators Classical
open CollisionCharacterStructure CarryBoundarySpectra

def boundaryDifferencePairing {m : ℕ} [NeZero m] (w₁ w₂ : ZMod m → ℂ) :
    (UnitClass m → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ u : UnitClass m, (signedBoundary w₁ u.val - signedBoundary w₂ u.val) * v u
  map_add' v z := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

theorem boundary_difference_pairing_character {m : ℕ} [NeZero m]
    (w₁ w₂ : ZMod m → ℂ) (χ : Character m) :
    boundaryDifferencePairing w₁ w₂ (fun u => χ u.val) =
      cellBoundaryFlux w₁ χ - cellBoundaryFlux w₂ χ := by
  simp only [cellBoundaryFlux_eq_boundary_pairing, sum_character_pairing_eq_units,
    boundaryDifferencePairing, LinearMap.coe_mk, AddHom.coe_mk,
    sub_mul, Finset.sum_sub_distrib]

/-- Title: `Equality on a character family is boundary orthogonality on that family`. -/
theorem family_flux_equality_iff {m : ℕ} [NeZero m]
    (w₁ w₂ : ZMod m → ℂ) (X : Set (Character m)) :
    (∀ χ ∈ X, cellBoundaryFlux w₁ χ = cellBoundaryFlux w₂ χ) ↔
      ∀ χ ∈ X, (∑ u : UnitClass m,
        (signedBoundary w₁ u.val - signedBoundary w₂ u.val) * χ u.val) = 0 := by
  change (∀ χ ∈ X, cellBoundaryFlux w₁ χ = cellBoundaryFlux w₂ χ) ↔
    ∀ χ ∈ X, boundaryDifferencePairing w₁ w₂ (fun u => χ u.val) = 0
  simp only [boundary_difference_pairing_character, sub_eq_zero]

/-- Title: `The selected character span lies in the boundary difference kernel`.
This is the usual Hermitian orthogonality to conjugated characters, written
as the equivalent complex-linear pairing with the original characters. -/
theorem family_flux_span_kernel {m : ℕ} [NeZero m]
    (w₁ w₂ : ZMod m → ℂ) (X : Set (Character m)) :
    (∀ χ ∈ X, cellBoundaryFlux w₁ χ = cellBoundaryFlux w₂ χ) ↔
      Submodule.span ℂ ((fun χ : Character m => fun u : UnitClass m => χ u.val) '' X) ≤
        LinearMap.ker (boundaryDifferencePairing w₁ w₂) := by
  rw [Submodule.span_le]
  constructor
  · intro h v hv
    obtain ⟨χ, hχ, rfl⟩ := hv
    change boundaryDifferencePairing w₁ w₂ (fun u => χ u.val) = 0
    rw [boundary_difference_pairing_character, h χ hχ, sub_self]
  · intro h χ hχ
    have hz := h (Set.mem_image_of_mem (fun ψ : Character m => fun u : UnitClass m => ψ u.val) hχ)
    change boundaryDifferencePairing w₁ w₂ (fun u => χ u.val) = 0 at hz
    rw [boundary_difference_pairing_character] at hz
    exact sub_eq_zero.mp hz

end NField.Alignment.CarryBoundaryFamily
