/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanExtensionTrace

/-!
# Actual quadratic root families and the curve-count power-sum bound

The roots are selected over the prime field once per nonzero frequency.
The same family works over every finite extension. The exact curve count
and Stepanov estimate therefore control the aggregate of their powers.
An individual root-modulus bound still requires the growth argument.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanRootPowerAggregate
open scoped BigOperators Classical
open KloostermanQuadraticLSeries KloostermanTraceSum KloostermanExtensionTrace
  KloostermanCurve

/-- One root family for all nonzero frequencies, with actual L-series
factorizations and exact sum and product. -/
theorem exists_root_families (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) :
    ∃ α β : ZMod p → ℂ, ∀ m : ZMod p, m≠0 →
      α m+β m = -traceKloostermanSum p a b m ∧ α m*β m=p ∧
      formalLSeries p a b m =
        (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X) := by
  choose α β h using (fun m : ZMod p => exists_quadratic_factors p a b m)
  refine ⟨α,β,?_⟩
  intro m hm
  refine ⟨(h m).1,(h m).2.1,?_⟩
  rw [formalLSeries_eq_quadratic p a b m ha hb hm,(h m).2.2]
  simp

/-- Sum the proved extension-field trace formula over every nonzero frequency. -/
theorem nonzero_trace_sum_eq_neg_root_powers {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (a b : ZMod p) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    (∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m) =
      -∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        (α m^(Module.finrank (ZMod p) K)+β m^(Module.finrank (ZMod p) K)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact traceKloostermanSum_eq_root_powers p a b m (α m) (β m)
    (hf m (Finset.mem_erase.mp hm).1)

/-- The literal Kloosterman curve count is q-1 minus the aggregate powers
of the actual reciprocal roots. -/
theorem curve_pointCount_eq_root_powers {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] (a b : ZMod p) (ha : a≠0) (hb : b≠0)
    (h2 : (2:K)≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    (StepanovPointCount.pointCount (curvePolynomial p
      (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b)) : ℂ) =
      (Fintype.card K:ℂ)-1-
        ∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          (α m^(Module.finrank (ZMod p) K)+β m^(Module.finrank (ZMod p) K)) := by
  have hab : algebraMap (ZMod p) K a*algebraMap (ZMod p) K b≠0 := by
    exact mul_ne_zero (by simpa using ha) (by simpa using hb)
  have h := nonzero_trace_sum_sub_one p
    (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) hab h2
  rw [nonzero_trace_sum_eq_neg_root_powers p a b α β hf] at h
  linear_combination -h

/-- Stepanov's bound now applies to the actual reciprocal-root power
aggregate. It does not yet bound individual roots or individual sums. -/
theorem root_power_aggregate_bound {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] (a b : ZMod p) (ha : a≠0) (hb : b≠0)
    (hodd : Odd (Fintype.card K)) (hq : 12*p≤Fintype.card K)
    (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ‖(∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      (α m^(Module.finrank (ZMod p) K)+β m^(Module.finrank (ZMod p) K)))+1‖ <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) := by
  have hab : algebraMap (ZMod p) K a*algebraMap (ZMod p) K b≠0 := by
    exact mul_ne_zero (by simpa using ha) (by simpa using hb)
  have h := nonzero_trace_sum_bound p
    (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) hab hodd hq
  rw [nonzero_trace_sum_eq_neg_root_powers p a b α β hf] at h
  simpa only [sub_eq_add_neg, ← neg_add, norm_neg] using h

end NField.Alignment.KloostermanRootPowerAggregate
