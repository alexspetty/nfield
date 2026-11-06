/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerPositiveFrequencies
import NField.Alignment.CollisionDirichletBoundary

/-! # Partial summation for real reciprocal exponential blocks

The prefix cancellation estimate is an explicit hypothesis. The phase is a
real reciprocal, summed over all integers, without modular unit restrictions.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalWeightedBlocks
open scoped BigOperators Classical

theorem truncated_prefix (z : ℕ → ℂ) (M n : ℕ) :
    (∑ i ∈ Finset.range n, if i < M then z i else 0) =
      ∑ i ∈ Finset.range (min n M), z i := by
  rw [← Finset.sum_filter]
  have he : (Finset.range n).filter (fun i => i < M) = Finset.range (min n M) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]

/-- Uniform finite prefix cancellation transfers to reciprocal weights at
cost `1/(p+1)`. No prefixes beyond the given block are required. -/
theorem weighted_block_from_prefix (z : ℕ → ℂ) (p M : ℕ) (B : ℝ)
    (hB : ∀ n ≤ M, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range M, (((p+i+1 : ℕ) : ℝ)⁻¹ : ℂ)*z i‖ ≤
      B / (p+1 : ℕ) := by
  have hf0 : ∀ i : ℕ, 0 ≤ (((p+i+1 : ℕ) : ℝ)⁻¹) := by intro i; positivity
  have hfa : Antitone (fun i : ℕ => (((p+i+1 : ℕ) : ℝ)⁻¹)) := by
    intro i j hij
    apply inv_anti₀ (by positivity)
    exact_mod_cast (by omega : p+i+1 ≤ p+j+1)
  have hz : ∀ n, ‖∑ i ∈ Finset.range n, if i < M then z i else 0‖ ≤ B := by
    intro n
    rw [truncated_prefix]
    exact hB _ (min_le_right _ _)
  have hh := CollisionDirichletBoundary.norm_sum_range_smul_le hf0 hfa hz M
  have he : (∑ i ∈ Finset.range M, (((p+i+1 : ℕ) : ℝ)⁻¹) •
      (if i < M then z i else 0)) =
      ∑ i ∈ Finset.range M, ((((p+i+1 : ℕ) : ℝ)⁻¹) : ℂ)*z i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi), Complex.real_smul]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [he] at hh
  simpa only [Nat.add_zero, div_eq_mul_inv] using hh

def reciprocalPhase (Q : ℝ) (n : ℕ) : ℂ :=
  fourier 1 ((Q / n : ℝ) : AddCircle (1 : ℝ))

def reciprocalPrefix (p M : ℕ) (Q : ℝ) : ℂ :=
  ∑ i ∈ Finset.range M, reciprocalPhase Q (p+i+1)

def weightedReciprocalBlock (p M : ℕ) (Q : ℝ) : ℂ :=
  ∑ i ∈ Finset.range M, ((((p+i+1 : ℕ) : ℝ)⁻¹) : ℂ)*reciprocalPhase Q (p+i+1)

/-- The actual real reciprocal block inherits the finite prefix estimate. -/
theorem weighted_reciprocal_from_prefix (p M : ℕ) (Q B : ℝ)
    (hB : ∀ n ≤ M, ‖reciprocalPrefix p n Q‖ ≤ B) :
    ‖weightedReciprocalBlock p M Q‖ ≤ B / (p+1 : ℕ) :=
  weighted_block_from_prefix _ p M B hB

/-- Source-shaped unweighted cancellation implies the weighted block bound.
The analytic cancellation hypothesis is retained explicitly. -/
theorem weighted_reciprocal_decay (p M : ℕ) (Q C A : ℝ)
    (hQ : 0 < Q) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hprefix : ∀ n ≤ M, ‖reciprocalPrefix p n Q‖ ≤
      C*((p : ℝ)*A+(p : ℝ)^2/Q)) :
    ‖weightedReciprocalBlock p M Q‖ ≤ C*(A+(p : ℝ)/Q) := by
  apply (weighted_reciprocal_from_prefix p M Q _ hprefix).trans
  have hp : (0 : ℝ) < p+1 := by positivity
  push_cast
  apply (div_le_iff₀ hp).mpr
  have he : (p : ℝ)^2/Q = (p : ℝ)*((p : ℝ)/Q) := by ring
  rw [he]
  nlinarith [div_nonneg (Nat.cast_nonneg p) hQ.le]

/-- The exponential-decay form required by the Saffari--Vaughan block argument.
The real reciprocal cancellation bound is still an explicit hypothesis. -/
theorem weighted_reciprocal_exponential (p M : ℕ) (Q C γ : ℝ)
    (hQ : 0 < Q) (hC : 0 ≤ C)
    (hprefix : ∀ n ≤ M, ‖reciprocalPrefix p n Q‖ ≤
      C*((p : ℝ)*Real.exp (-γ*(Real.log p)^3/(Real.log Q)^2)+(p : ℝ)^2/Q)) :
    ‖weightedReciprocalBlock p M Q‖ ≤
      C*(Real.exp (-γ*(Real.log p)^3/(Real.log Q)^2)+(p : ℝ)/Q) :=
  weighted_reciprocal_decay p M Q C _ hQ hC (Real.exp_nonneg _) hprefix

end NField.Alignment.ReciprocalWeightedBlocks
