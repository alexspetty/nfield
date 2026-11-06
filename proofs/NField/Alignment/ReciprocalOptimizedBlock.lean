/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalFourierCutoff
import Mathlib.Analysis.PSeries

/-! # Optimized reciprocal distribution block
The unweighted reciprocal cancellation estimate remains a visible hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalOptimizedBlock
open ReciprocalFourierCutoff ReciprocalBlockDiscrepancy ReciprocalWeightedBlocks
open scoped BigOperators Classical

theorem reciprocal_square_sum (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)^2)⁻¹) ≤ 2 := by
  have he : Finset.Icc 1 H = Finset.Ioo 0 (H+1) := by ext h; simp; omega
  rw [he]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (H+1))

theorem frequency_cost (H : ℕ) (C A B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    (∑ h ∈ Finset.Icc 1 H, C*(A+B/h)/h) ≤
      C*(A*(∑ h ∈ Finset.Icc 1 H, (h : ℝ)⁻¹)+2*B) := by
  have he : (∑ h ∈ Finset.Icc 1 H, C*(A+B/h)/h) =
      C*(A*(∑ h ∈ Finset.Icc 1 H, (h : ℝ)⁻¹)+
        B*(∑ h ∈ Finset.Icc 1 H, ((h : ℝ)^2)⁻¹)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (reciprocal_square_sum H) hB
  nlinarith

theorem trivial_block_discrepancy (p M : ℕ) (hM : M ≤ p+1) (x α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |blockDistribution p M x α - α*blockMass p M| ≤ 1 := by
  have hb : 0 ≤ blockDistribution p M x α ∧ blockDistribution p M x α ≤ blockMass p M := by
    unfold blockDistribution FejerWeightedDiscrepancy.thresholdSum blockMass
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    · apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> simp only [mul_one, mul_zero, le_refl, inv_nonneg, Nat.cast_nonneg]
  have hw := block_mass_nonneg p M
  have hw1 := block_mass_le_one p M hM
  have ha := mul_le_mul_of_nonneg_right hα1 hw
  have ha0 := mul_nonneg hα0 hw
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Full block optimization, conditional only on the actual reciprocal-prefix
cancellation for the chosen finite frequencies and endpoints. -/
theorem optimized_block (p M : ℕ) (hp : 1 ≤ p) (hM : M ≤ p+1)
    (x α C γ : ℝ) (hx : 1 < x) (hpx : (p : ℝ) ≤ x)
    (hC : 0 ≤ C) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hprefix : ∀ h ∈ Finset.Icc 1 (cutoff (γ*(Real.log p)^3/(16*(Real.log x)^2))),
      ∀ n ≤ M, ‖reciprocalPrefix p n ((h : ℝ)*x)‖ ≤
        C*((p : ℝ)*Real.exp (-γ*(Real.log p)^3/(Real.log ((h : ℝ)*x))^2)+
          (p : ℝ)^2/((h : ℝ)*x))) :
    |blockDistribution p M x α - α*blockMass p M| ≤
      (8+8*C)*(Real.exp (-(γ*(Real.log p)^3/(16*(Real.log x)^2)))+(p : ℝ)/x) := by
  let η := γ*(Real.log p)^3/(16*(Real.log x)^2)
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηx : η ≤ Real.log x/16 := optimized_exponent_upper γ _ _ hγ0 hγ1 hlp
    (Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpx) hlx
  have hB : 0 ≤ (p : ℝ)/x := by positivity
  by_cases hH : 16 ≤ cutoff η
  · have hb := block_discrepancy_from_prefix p M (cutoff η) hM hH x α C γ
      (by linarith) hC hα0 hα1 hprefix
    have hsave : ∀ h ∈ Finset.Icc 1 (cutoff η),
        Real.exp (-γ*(Real.log p)^3/(Real.log ((h : ℝ)*x))^2) ≤ Real.exp (-4*η) := by
      intro h hh
      have hh1 := (Finset.mem_Icc.mp hh).1
      have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
      apply frequency_exponential_saving γ _ _ _ hγ0 hlp hlx
      · apply Real.log_pos
        nlinarith
      · exact frequency_log_bound η x hη hx hηx h hh1 (Finset.mem_Icc.mp hh).2
    have hsum : (∑ h ∈ Finset.Icc 1 (cutoff η),
        C*(Real.exp (-γ*(Real.log p)^3/(Real.log ((h : ℝ)*x))^2)+(p : ℝ)/((h : ℝ)*x))/h) ≤
        C*(Real.exp (-η)+2*((p : ℝ)/x)) := by
      calc
        _ ≤ ∑ h ∈ Finset.Icc 1 (cutoff η), C*(Real.exp (-4*η)+((p : ℝ)/x)/h)/h := by
          apply Finset.sum_le_sum
          intro h hh
          have he : (p : ℝ)/((h : ℝ)*x) = ((p : ℝ)/x)/h := by ring
          rw [he]
          gcongr
          exact Real.exp_le_exp.mp (hsave h hh)
        _ ≤ C*(Real.exp (-4*η)*(∑ h ∈ Finset.Icc 1 (cutoff η), (h : ℝ)⁻¹)+2*((p : ℝ)/x)) :=
          frequency_cost _ _ _ _ hC hB
        _ ≤ _ := by
          have hh := harmonic_exponential_cost η hη
          rw [mul_comm (Real.exp (-4*η))]
          gcongr
    have hs := cutoff_smoothing η hη
    have he := Real.exp_pos (-η)
    nlinarith
  · have hb := trivial_block_discrepancy p M hM x α hα0 hα1
    have hh := small_cutoff_cost η hη (by omega)
    have he := Real.exp_pos (-η)
    nlinarith

end NField.Alignment.ReciprocalOptimizedBlock
