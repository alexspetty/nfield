/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactPrefixWitness
import NField.ResetForests.CostPopulations
/-! # The four prescribed physical prefix projections at p=61 -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open RecordGeometry PrefixGeometry

def cost61Metric : Matrix (Fin 60) (Fin 60) ℝ := SourceMetrics.sampledGram 60 3721

theorem cost61_metric_positive : cost61Metric.PosDef :=
  (SourceMetrics.both_prime_square_grams_posDef cost61_prime (by decide)).2

def cost61Prefixes : ℕ → Finset (PhysicalIndex 61 {1}) :=
  physicalPrefixes 61 {1} (dyadicCuts 5)

theorem cost61_prefixes_zero : cost61Prefixes 0 = ∅ :=
  physical_prefix_zero _ _ _ (dyadic_cuts_zero _)

theorem cost61_prefixes_monotone : Monotone cost61Prefixes :=
  physical_prefix_monotone _ _ _ (dyadic_cuts_monotone _)

theorem cost61_prefixes_final : cost61Prefixes 4 = Finset.univ := by
  apply physical_prefix_final
  rw [cost61_ordered]
  decide

def cost61ActualSource (r : ℕ) : Fin 60 → ℝ :=
  prefixSource cost61Metric cost61_metric_positive (physicalRecord 61 {1})
    cost61Prefixes (fun _ => 1) r

def cost61ActualEnergy (r : ℕ) : ℝ :=
  sourceWork cost61Metric (cost61ActualSource r) (cost61ActualSource r)

def cost61ActualReading (r : ℕ) : ℝ :=
  finalReadout (physicalRecord 61 {1}) (physicalReadoutWeights 61 {1}) (cost61ActualSource r)

def cost61ActualCost : ℝ :=
  prefixCost cost61Metric cost61_metric_positive (physicalRecord 61 {1})
    (physicalReadoutWeights 61 {1}) cost61Prefixes (fun _ => 1) 4

def cost61ActualObservedWork : ℝ :=
  ∑ r ∈ Finset.range 4,
    sourceWork cost61Metric
      (prefixIncrement cost61Metric cost61_metric_positive (physicalRecord 61 {1})
        cost61Prefixes (fun _ => 1) r)
      (prefixIncrement cost61Metric cost61_metric_positive (physicalRecord 61 {1})
        cost61Prefixes (fun _ => 1) r)

def cost61ActualD : ℝ :=
  finalReadout (physicalRecord 61 {1}) (physicalReadoutWeights 61 {1}) (fun _ => 1)

theorem cost61_source_zero : cost61ActualSource 0 = 0 :=
  prefix_zero _ _ _ _ cost61_prefixes_zero _

theorem cost61_energy_zero : cost61ActualEnergy 0 = 0 := by
  rw [cost61ActualEnergy, cost61_source_zero]
  simp [sourceWork]

theorem cost61_reading_zero : cost61ActualReading 0 = 0 := by
  rw [cost61ActualReading, cost61_source_zero, map_zero]

theorem cost61_final_reading : cost61ActualReading 4 = cost61ActualD := by
  change _ ⬝ᵥ ((physicalRecord 61 {1}) *ᵥ
    oldSource cost61Metric cost61_metric_positive
      (restrictedRecord (physicalRecord 61 {1}) (cost61Prefixes 4)) (fun _ => 1)) = _
  rw [cost61_prefixes_final, restricted_univ, old_source_reading]
  rfl

theorem cost61_observed_work : cost61ActualObservedWork = cost61ActualEnergy 4 := by
  unfold cost61ActualObservedWork
  simp_rw [prefix_increment_energy _ _ _ _ cost61_prefixes_monotone]
  change (∑ r ∈ Finset.range 4, (cost61ActualEnergy (r + 1) - cost61ActualEnergy r)) = _
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.reduceAdd,
    cost61_energy_zero]
  ring

theorem cost61_actual_four_quotients :
    cost61ActualCost =
      cost61ActualReading 1 ^ 2 / cost61ActualEnergy 1 +
      (cost61ActualReading 2 - cost61ActualReading 1)^2 /
        (cost61ActualEnergy 2 - cost61ActualEnergy 1) +
      (cost61ActualReading 3 - cost61ActualReading 2)^2 /
        (cost61ActualEnergy 3 - cost61ActualEnergy 2) +
      (cost61ActualReading 4 - cost61ActualReading 3)^2 /
        (cost61ActualEnergy 4 - cost61ActualEnergy 3) := by
  unfold cost61ActualCost
  rw [prefix_increment_cost_formula _ _ _ _ _ cost61_prefixes_monotone]
  change (∑ r ∈ Finset.range 4,
    (cost61ActualReading (r + 1) - cost61ActualReading r)^2 /
      (cost61ActualEnergy (r + 1) - cost61ActualEnergy r)) = _
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.reduceAdd,
    cost61_energy_zero, cost61_reading_zero, sub_zero, zero_add]

end NField.ResetForests.ExactCost
