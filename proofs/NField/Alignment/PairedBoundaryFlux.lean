/-
Author: Alexander S. Petty
-/

import NField.Alignment.PairedBoundary

/-!
# Flux of a paired finite boundary

This module turns a signed indicator boundary into the corresponding endpoint
sum.  An antipodal pairing then gives the exact factor two against every odd
test function.  The statements are independent of collision geometry and can
be reused by any concrete boundary object.
-/

namespace NField.Alignment.PairedBoundaryFlux

open scoped BigOperators
open NField.Alignment.PairedBoundary

/-- Pairing an image indicator with a test function evaluates the function at
every source point, with multiplicity. -/
theorem imageIndicator_pairing
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (F : κ → ℂ) :
    (∑ x : κ, imageIndicator f x * F x) = ∑ i : ι, F (f i) := by
  classical
  unfold imageIndicator
  calc
    (∑ x : κ, (∑ i : ι, if f i = x then 1 else 0) * F x) =
        ∑ x : κ, ∑ i : ι, (if f i = x then 1 else 0) * F x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ i : ι, ∑ x : κ,
        (if f i = x then 1 else 0) * F x := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, F (f i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp

/-- A signed paired boundary acts by right endpoint minus left endpoint. -/
theorem pairedBoundary_pairing
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (L R : ι → κ) (F : κ → ℂ) :
    (∑ x : κ, pairedBoundary L R x * F x) =
      ∑ i : ι, (F (R i) - F (L i)) := by
  classical
  unfold pairedBoundary
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [imageIndicator_pairing, imageIndicator_pairing]

/-- If the right endpoints are the antipodes of the left endpoints, every odd
test function sees exactly negative twice the left endpoint sum. -/
theorem pairedBoundary_pairing_odd
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [InvolutiveNeg κ]
    (L R : ι → κ) (σ : ι ≃ ι)
    (hpair : ∀ i, -L i = R (σ i))
    (F : κ → ℂ) (hodd : ∀ x, F (-x) = -F x) :
    (∑ x : κ, pairedBoundary L R x * F x) =
      -2 * ∑ i : ι, F (L i) := by
  classical
  rw [pairedBoundary_pairing]
  have hright : (∑ i : ι, F (R i)) = -∑ i : ι, F (L i) := by
    calc
      (∑ i : ι, F (R i)) = ∑ i : ι, F (R (σ i)) := by
        exact (σ.sum_comp (fun i => F (R i))).symm
      _ = ∑ i : ι, F (-L i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hpair]
      _ = ∑ i : ι, -F (L i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hodd]
      _ = -∑ i : ι, F (L i) := by rw [Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib, hright]
  ring

end NField.Alignment.PairedBoundaryFlux
