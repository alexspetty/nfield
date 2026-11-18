/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.CostPhysical61
import NField.ResetForests.CostWitness61
/-! # The printed decimals belong to the actual source and complete detector -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open RecordGeometry PrefixGeometry

theorem cost61_realize_prefix (r n : ℕ) (hcut : dyadicCuts 5 r = n)
    (C : Finset ℕ) (hprefix : prefixClocks 61 {1} n = C)
    (z : Fin 60 → ℚ) (w : ℕ → Bool → ℚ)
    (hz : cost61Gram *ᵥ z = fun j => ∑ k ∈ C,
      (cost61Row k false j * w k false + cost61Row k true j * w k true))
    (hc : ∀ k ∈ C, ∀ b, cost61Row k b ⬝ᵥ z = cost61Row k b ⬝ᵥ (fun _ => 1)) :
    cost61ActualSource r = castVector z := by
  have h := rational_actual_prefix_witness cost61_prime (by decide) {1}
    (dyadicCuts 5) r (fun _ => 1) z w
  have hone : castVector (fun _ : Fin 60 => (1 : ℚ)) = (fun _ => (1 : ℝ)) := by
    funext j
    simp only [castVector, Rat.cast_one]
  rw [hone] at h
  apply h
  · intro k hk
    exact cost61_chosen_positive k (prefix_clocks_subset _ _ _ hk)
  · change exactGram 60 3721 *ᵥ z = _
    rw [cost61_gram_exact, hcut, hprefix]
    rw [hz]
    funext j
    apply Finset.sum_congr rfl
    intro k hk
    have hm : k ∈ chosenClocks 61 {1} :=
      prefix_clocks_subset _ _ n (by rw [hprefix]; exact hk)
    rw [cost61_row_table hm false j, cost61_row_table hm true j]
  · intro k hk b
    rw [hcut, hprefix] at hk
    have hm : k ∈ chosenClocks 61 {1} :=
      prefix_clocks_subset _ _ n (by rw [hprefix]; exact hk)
    have hh : rationalClockRow 61 k b = cost61Row k b := funext (cost61_row_table hm b)
    rw [hh]
    exact hc k hk b

theorem cost61_realize_energy (r : ℕ) (z : Fin 60 → ℚ) (E : ℚ)
    (hs : cost61ActualSource r = castVector z)
    (he : z ⬝ᵥ (cost61Gram *ᵥ z) = E) : cost61ActualEnergy r = (E : ℝ) := by
  rw [cost61ActualEnergy, hs]
  unfold cost61Metric
  rw [sampled_gram_exact (by norm_num : 0 < 3721), cost61_gram_exact,
    rational_source_work, he]

theorem cost61_readout_table (z : Fin 60 → ℚ) :
    rationalReadout 61 (chosenClocks 61 {1}) z =
      4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ),
        cost61Row k true ⬝ᵥ z := by
  rw [← cost61_chosen, Finset.mul_sum]
  unfold rationalReadout
  apply Finset.sum_congr rfl
  intro k hk
  have hm : (60 / k : ℕ) = 1 := cost61_chosen_load k hk
  have hr : rationalClockRow 61 k true = cost61Row k true := funext (cost61_row_table hk true)
  change 4 * ((60 / k : ℕ) : ℚ) * (rationalClockRow 61 k true ⬝ᵥ z) = _
  rw [hm, Nat.cast_one, mul_one, hr]

theorem cost61_realize_reading (r : ℕ) (z : Fin 60 → ℚ) (F : ℚ)
    (hs : cost61ActualSource r = castVector z)
    (hf : 4 * ∑ k ∈ ({51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} : Finset ℕ),
      cost61Row k true ⬝ᵥ z = F) : cost61ActualReading r = (F : ℝ) := by
  rw [cost61ActualReading, hs, physical_readout_rational _ _ cost61_chosen_positive,
    cost61_readout_table, hf]

theorem cost61_source_at_1 : cost61ActualSource 1 = castVector cost61Source1 :=
  cost61_realize_prefix 1 1 (by decide) _ cost61_prefix1
    _ _ cost61_metric_witness1 cost61_readback_witness1

theorem cost61_energy_at_1 : cost61ActualEnergy 1 = (cost61Energy1 : ℝ) :=
  cost61_realize_energy _ _ _ cost61_source_at_1 cost61_energy_witness1

theorem cost61_reading_at_1 : cost61ActualReading 1 = (cost61Reading1 : ℝ) :=
  cost61_realize_reading _ _ _ cost61_source_at_1 cost61_reading_witness1

theorem cost61_source_at_2 : cost61ActualSource 2 = castVector cost61Source2 :=
  cost61_realize_prefix 2 2 (by decide) _ cost61_prefix2
    _ _ cost61_metric_witness2 cost61_readback_witness2

theorem cost61_energy_at_2 : cost61ActualEnergy 2 = (cost61Energy2 : ℝ) :=
  cost61_realize_energy _ _ _ cost61_source_at_2 cost61_energy_witness2

theorem cost61_reading_at_2 : cost61ActualReading 2 = (cost61Reading2 : ℝ) :=
  cost61_realize_reading _ _ _ cost61_source_at_2 cost61_reading_witness2

theorem cost61_source_at_3 : cost61ActualSource 3 = castVector cost61Source4 :=
  cost61_realize_prefix 3 4 (by decide) _ cost61_prefix4
    _ _ cost61_metric_witness4 cost61_readback_witness4

theorem cost61_energy_at_3 : cost61ActualEnergy 3 = (cost61Energy4 : ℝ) :=
  cost61_realize_energy _ _ _ cost61_source_at_3 cost61_energy_witness4

theorem cost61_reading_at_3 : cost61ActualReading 3 = (cost61Reading4 : ℝ) :=
  cost61_realize_reading _ _ _ cost61_source_at_3 cost61_reading_witness4

theorem cost61_source_at_4 : cost61ActualSource 4 = castVector cost61Source5 :=
  cost61_realize_prefix 4 5 (by decide) _ cost61_prefix5
    _ _ cost61_metric_witness5 cost61_readback_witness5

theorem cost61_energy_at_4 : cost61ActualEnergy 4 = (cost61Energy5 : ℝ) :=
  cost61_realize_energy _ _ _ cost61_source_at_4 cost61_energy_witness5

theorem cost61_reading_at_4 : cost61ActualReading 4 = (cost61Reading5 : ℝ) :=
  cost61_realize_reading _ _ _ cost61_source_at_4 cost61_reading_witness5

theorem cost61_actual_cost_exact : cost61ActualCost = (cost61ExactCost : ℝ) := by
  rw [cost61_actual_four_quotients, cost61_energy_at_1, cost61_energy_at_2,
    cost61_energy_at_3, cost61_energy_at_4, cost61_reading_at_1, cost61_reading_at_2,
    cost61_reading_at_3, cost61_reading_at_4]
  unfold cost61ExactCost
  push_cast
  rfl

theorem cost61_actual_ratio_exact :
    cost61ActualD ^ 2 / cost61ActualObservedWork = (cost61ExactRatio : ℝ) := by
  rw [← cost61_final_reading, cost61_reading_at_4, cost61_observed_work, cost61_energy_at_4]
  unfold cost61ExactRatio
  push_cast
  rfl

theorem cost61_actual_observed_work_positive : 0 < cost61ActualObservedWork := by
  rw [cost61_observed_work, cost61_energy_at_4]
  have h := cost61_energy_increments_positive
  have he : (0 : ℚ) < cost61Energy5 := h.1.trans (h.2.1.trans (h.2.2.1.trans h.2.2.2))
  exact_mod_cast he

theorem cost61_actual_decimal_cost :
    (38176649888 / 10000000000 : ℝ) < cost61ActualCost ∧
      cost61ActualCost < (38176649889 / 10000000000 : ℝ) := by
  rw [cost61_actual_cost_exact]
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_lt (K := ℝ)).mpr cost61_decimal_cost.1)
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_lt (K := ℝ)).mpr cost61_decimal_cost.2)

theorem cost61_actual_decimal_ratio :
    (7201556918 / 10000000000 : ℝ) < cost61ActualD^2 / cost61ActualObservedWork ∧
      cost61ActualD^2 / cost61ActualObservedWork < (7201556919 / 10000000000 : ℝ) := by
  rw [cost61_actual_ratio_exact]
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_lt (K := ℝ)).mpr cost61_decimal_ratio.1)
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_lt (K := ℝ)).mpr cost61_decimal_ratio.2)

end NField.ResetForests.ExactCost
