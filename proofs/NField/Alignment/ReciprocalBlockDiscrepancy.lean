/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalWeightedBlocks

/-! # Actual reciprocal-block distribution from prefix cancellation -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalBlockDiscrepancy
open ReciprocalWeightedBlocks FejerPositiveFrequencies FejerWeightedDiscrepancy
open scoped BigOperators Classical

def blockMass (p M : ℕ) : ℝ := ∑ i ∈ Finset.range M, ((p+i+1 : ℕ) : ℝ)⁻¹

def blockDistribution (p M : ℕ) (x α : ℝ) : ℝ :=
  thresholdSum (Finset.range M) (fun i => ((p+i+1 : ℕ) : ℝ)⁻¹)
    (fun i => x / ((p+i+1 : ℕ) : ℝ)) α

theorem block_mass_nonneg (p M : ℕ) : 0 ≤ blockMass p M := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

/-- Any initial portion of a dyadic block has bounded harmonic mass. -/
theorem block_mass_le_one (p M : ℕ) (hM : M ≤ p+1) : blockMass p M ≤ 1 := by
  have hp : (0 : ℝ) < (p+1 : ℕ) := by positivity
  calc
    _ ≤ ∑ i ∈ Finset.range M, (((p+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      apply inv_anti₀ hp
      exact_mod_cast (by omega : p+1 ≤ p+i+1)
    _ = (M : ℝ) / (p+1 : ℕ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hp).mpr (by exact_mod_cast hM)

/-- Fourier frequency multiplication is the actual real reciprocal phase. -/
theorem reciprocal_frequency (h n : ℕ) (x : ℝ) :
    fourier (h : ℤ) ((x/n : ℝ) : AddCircle (1 : ℝ)) = reciprocalPhase ((h : ℝ)*x) n := by
  unfold reciprocalPhase
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

theorem block_positive_error (p M H : ℕ) (x : ℝ) :
    positiveError (Finset.range M) (fun i => ((p+i+1 : ℕ) : ℝ)⁻¹)
      (fun i => ((x/((p+i+1 : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ))) H =
      ∑ h ∈ Finset.Icc 1 H, ‖weightedReciprocalBlock p M ((h : ℝ)*x)‖ / h := by
  unfold positiveError weightedReciprocalBlock
  simp_rw [reciprocal_frequency]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The checked discrepancy theorem applied to the literal reciprocal samples. -/
theorem block_discrepancy (p M H : ℕ) (hH : 16 ≤ H) (x α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |blockDistribution p M x α - α*blockMass p M| ≤
      4*((Real.sqrt (H : ℝ))⁻¹*blockMass p M +
        ∑ h ∈ Finset.Icc 1 H, ‖weightedReciprocalBlock p M ((h : ℝ)*x)‖/h) := by
  have hh := weighted_discrepancy (Finset.range M)
    (fun i => ((p+i+1 : ℕ) : ℝ)⁻¹) (fun i => x/((p+i+1 : ℕ) : ℝ))
    (fun i hi => by positivity) H hH α hα0 hα1
  rw [block_positive_error] at hh
  exact hh

/-- Conditional block distribution bound from the real reciprocal prefix estimate.
Every frequency and endpoint prefix retains the analytic hypothesis. -/
theorem block_discrepancy_from_prefix (p M H : ℕ) (hM : M ≤ p+1) (hH : 16 ≤ H)
    (x α C γ : ℝ) (hx : 0 < x) (hC : 0 ≤ C) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hprefix : ∀ h ∈ Finset.Icc 1 H, ∀ n ≤ M,
      ‖reciprocalPrefix p n ((h : ℝ)*x)‖ ≤
        C*((p : ℝ)*Real.exp (-γ*(Real.log p)^3/(Real.log ((h : ℝ)*x))^2)+
          (p : ℝ)^2/((h : ℝ)*x))) :
    |blockDistribution p M x α - α*blockMass p M| ≤
      4*((Real.sqrt (H : ℝ))⁻¹ +
        ∑ h ∈ Finset.Icc 1 H,
          C*(Real.exp (-γ*(Real.log p)^3/(Real.log ((h : ℝ)*x))^2)+
            (p : ℝ)/((h : ℝ)*x))/h) := by
  apply (block_discrepancy p M H hH x α hα0 hα1).trans
  gcongr with h hh
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (block_mass_le_one p M hM)
      (show 0 ≤ (Real.sqrt (H : ℝ))⁻¹ by positivity)
  · have hh0 : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
    exact weighted_reciprocal_exponential p M ((h : ℝ)*x) C γ (mul_pos hh0 hx) hC (hprefix h hh)

end NField.Alignment.ReciprocalBlockDiscrepancy
