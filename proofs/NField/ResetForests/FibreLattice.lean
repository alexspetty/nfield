/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreLimits
/-! # Integral scaled coordinates, including midpoint contacts -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators
open NField.Alignment CommonResetGram CollisionRampEnergy FibreReconstruction

def integralRow (p j : ℕ) (u : ℝ) (v : ℕ) : ℤ :=
  2*(j : ℤ)*(v : ℤ)-2*(p : ℤ)*⌊(j : ℝ)*(((v : ℝ)+u)/(p : ℝ))⌋+
    2*⌊(j : ℝ)*u⌋-(p : ℤ)+1+
      (p : ℤ)*(if Int.fract ((j : ℝ)*(((v : ℝ)+u)/(p : ℝ)))=0 then 1 else 0)-
        (if Int.fract ((j : ℝ)*u)=0 then 1 else 0)

theorem twice_midpoint_floor (j : ℕ) (x : ℝ) :
    2*midpointRow j x=2*(j : ℝ)*x-2*(⌊(j : ℝ)*x⌋ : ℝ)-1+
      (if Int.fract ((j : ℝ)*x)=0 then 1 else 0) := by
  by_cases h : Int.fract ((j : ℝ)*x)=0
  · rw [midpointRow, if_pos h, if_pos h]
    unfold Int.fract at h
    linarith
  · rw [midpointRow, if_neg h, if_neg h]
    unfold affineRow Int.fract
    ring

theorem scaled_basis_fibre_integral {p : ℕ} (hp : 0 < p) (j : ℕ) (u : ℝ) (v : ℕ) :
    (p : ℝ)*(2*midpointRow j (((v : ℝ)+u)/(p : ℝ))-2*midpointRow j u/(p : ℝ))=
      (integralRow p j u v : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [twice_midpoint_floor, twice_midpoint_floor]
  unfold integralRow
  split_ifs <;> push_cast <;> field_simp <;> ring

theorem fibre_path_sum (p : ℕ) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) :
    fibrePath p c u v=
      ∑ j ∈ Finset.Icc 1 (p-1), c j*
        (2*midpointRow j (((v.val : ℝ)+u)/(p : ℝ))-2*midpointRow j u/(p : ℝ)) := by
  simp only [fibrePath, weightedProfile, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

theorem integral_source_scaled_coordinates {p : ℕ} (hp : 0 < p) (c : ℕ → ℤ)
    (u : ℝ) (v : Fin p) :
    (p : ℝ)*fibrePath p (fun j => (c j : ℝ)) u v=
      ((∑ j ∈ Finset.Icc 1 (p-1), c j*integralRow p j u v : ℤ) : ℝ) := by
  rw [fibre_path_sum, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, scaled_basis_fibre_integral hp]

theorem integral_source_scaled_zero_sum {p : ℕ} (hp : p.Prime) (c : ℕ → ℤ) (u : ℝ) :
    (∑ v : Fin p, ∑ j ∈ Finset.Icc 1 (p-1), c j*integralRow p j u v)=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_sum, Int.cast_zero]
  simp_rw [← integral_source_scaled_coordinates hp.pos]
  rw [← Finset.mul_sum, fibre_path_zero_sum hp, mul_zero]

end NField.ResetForests.FibreTraces
