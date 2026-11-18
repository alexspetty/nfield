/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactCostData61
import NField.ResetForests.CostPopulations
import NField.ResetForests.WitnessEnergy
/-! # Kernel checks of the concrete source witnesses and full detector readings -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open PrefixGeometry

theorem cost61_row_table {k : ℕ} (hk : k ∈ chosenClocks 61 {1}) :
    ∀ (b : Bool) (j : Fin 60), rationalClockRow 61 k b j = cost61Row k b j := by
  rw [cost61_chosen] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cost61_row_51
  · exact cost61_row_50
  · exact cost61_row_35
  · exact cost61_row_49
  · exact cost61_row_48
  · exact cost61_row_36
  · exact cost61_row_47
  · exact cost61_row_46
  · exact cost61_row_37
  · exact cost61_row_45
  · exact cost61_row_44
  · exact cost61_row_38
  · exact cost61_row_43
  · exact cost61_row_42
  · exact cost61_row_39

theorem cost61_metric_witness1 :
    cost61Gram *ᵥ cost61Source1 = fun j => ∑ k ∈ ({51, 50, 35} : Finset ℕ),
      (cost61Row k false j * cost61Weights1 k false + cost61Row k true j * cost61Weights1 k true) := by
  funext j
  revert j
  decide +kernel

theorem cost61_readback_witness1 : ∀ k ∈ ({51, 50, 35} : Finset ℕ), ∀ b : Bool,
    cost61Row k b ⬝ᵥ cost61Source1 = cost61Row k b ⬝ᵥ (fun _ => 1) := by decide +kernel

theorem cost61_energy_witness1 :
    cost61Source1 ⬝ᵥ (cost61Gram *ᵥ cost61Source1) = cost61Energy1 := by
  rw [paired_witness_energy _ _ _ _ _ cost61_metric_witness1 cost61_readback_witness1]
  decide +kernel

theorem cost61_reading_witness1 :
    4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ), cost61Row k true ⬝ᵥ cost61Source1 =
      cost61Reading1 := by decide +kernel

theorem cost61_metric_witness2 :
    cost61Gram *ᵥ cost61Source2 = fun j => ∑ k ∈ ({51, 50, 35, 49, 48, 36} : Finset ℕ),
      (cost61Row k false j * cost61Weights2 k false + cost61Row k true j * cost61Weights2 k true) := by
  funext j
  revert j
  decide +kernel

theorem cost61_readback_witness2 : ∀ k ∈ ({51, 50, 35, 49, 48, 36} : Finset ℕ), ∀ b : Bool,
    cost61Row k b ⬝ᵥ cost61Source2 = cost61Row k b ⬝ᵥ (fun _ => 1) := by decide +kernel

theorem cost61_energy_witness2 :
    cost61Source2 ⬝ᵥ (cost61Gram *ᵥ cost61Source2) = cost61Energy2 := by
  rw [paired_witness_energy _ _ _ _ _ cost61_metric_witness2 cost61_readback_witness2]
  decide +kernel

theorem cost61_reading_witness2 :
    4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ), cost61Row k true ⬝ᵥ cost61Source2 =
      cost61Reading2 := by decide +kernel

theorem cost61_metric_witness4 :
    cost61Gram *ᵥ cost61Source4 = fun j => ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38} : Finset ℕ),
      (cost61Row k false j * cost61Weights4 k false + cost61Row k true j * cost61Weights4 k true) := by
  funext j
  revert j
  decide +kernel

theorem cost61_readback_witness4 : ∀ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38} : Finset ℕ), ∀ b : Bool,
    cost61Row k b ⬝ᵥ cost61Source4 = cost61Row k b ⬝ᵥ (fun _ => 1) := by decide +kernel

theorem cost61_energy_witness4 :
    cost61Source4 ⬝ᵥ (cost61Gram *ᵥ cost61Source4) = cost61Energy4 := by
  rw [paired_witness_energy _ _ _ _ _ cost61_metric_witness4 cost61_readback_witness4]
  decide +kernel

theorem cost61_reading_witness4 :
    4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ), cost61Row k true ⬝ᵥ cost61Source4 =
      cost61Reading4 := by decide +kernel

theorem cost61_metric_witness5 :
    cost61Gram *ᵥ cost61Source5 = fun j => ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ),
      (cost61Row k false j * cost61Weights5 k false + cost61Row k true j * cost61Weights5 k true) := by
  funext j
  revert j
  decide +kernel

theorem cost61_readback_witness5 : ∀ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ), ∀ b : Bool,
    cost61Row k b ⬝ᵥ cost61Source5 = cost61Row k b ⬝ᵥ (fun _ => 1) := by decide +kernel

theorem cost61_energy_witness5 :
    cost61Source5 ⬝ᵥ (cost61Gram *ᵥ cost61Source5) = cost61Energy5 := by
  rw [paired_witness_energy _ _ _ _ _ cost61_metric_witness5 cost61_readback_witness5]
  decide +kernel

theorem cost61_reading_witness5 :
    4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ), cost61Row k true ⬝ᵥ cost61Source5 =
      cost61Reading5 := by decide +kernel

def cost61ExactCost : ℚ :=
  (cost61Reading1)^2 / (cost61Energy1) +
  (cost61Reading2 - cost61Reading1)^2 / (cost61Energy2 - cost61Energy1) +
  (cost61Reading4 - cost61Reading2)^2 / (cost61Energy4 - cost61Energy2) +
  (cost61Reading5 - cost61Reading4)^2 / (cost61Energy5 - cost61Energy4)

def cost61ExactRatio : ℚ := cost61Reading5^2 / cost61Energy5

theorem cost61_energy_increments_positive :
    0 < cost61Energy1 ∧ cost61Energy1 < cost61Energy2 ∧
      cost61Energy2 < cost61Energy4 ∧ cost61Energy4 < cost61Energy5 := by decide +kernel

theorem cost61_decimal_cost :
    (38176649888/10000000000 : ℚ) < cost61ExactCost ∧
      cost61ExactCost < (38176649889/10000000000 : ℚ) := by decide +kernel

theorem cost61_decimal_ratio :
    (7201556918/10000000000 : ℚ) < cost61ExactRatio ∧
      cost61ExactRatio < (7201556919/10000000000 : ℚ) := by decide +kernel

end NField.ResetForests.ExactCost
