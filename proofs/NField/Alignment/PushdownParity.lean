/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExactConductorEnergy

/-! # The precise pushdown vanishing criterion for primitive odd energy -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.PushdownParity
open scoped BigOperators ComplexConjugate
open CollisionCharacterStructure PrimitiveOddBoundaryMean ConductorBoundaryLedger ExactConductorEnergy

theorem boundaryFlux_even_zero {d : ℕ} [NeZero d]
    (μ : UnitClass d → ℂ) (hμ : ∀ x, μ (-x) = μ x)
    (χ : Character d) (hχ : χ.Odd) : boundaryFlux μ χ = 0 := by
  classical
  have hneg (x : UnitClass d) : χ (-x).val = -χ x.val := by
    change χ (-x.val) = _
    rw [← neg_one_mul, map_mul, hχ, neg_one_mul]
  have hself : boundaryFlux μ χ = -boundaryFlux μ χ := by
    unfold boundaryFlux
    calc
      _ = ∑ x : UnitClass d, μ (-x) * χ (-x).val :=
        (Equiv.sum_comp (Equiv.neg (UnitClass d)) (fun x => μ x * χ x.val)).symm
      _ = _ := by simp only [hμ, hneg, mul_neg, Finset.sum_neg_distrib]
  linear_combination (1 / 2 : ℂ) * hself

theorem exactConductorEnergy_zero_of_even_pushdown {m d : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (μ : UnitClass m → ℂ)
    (hμ : ∀ r, unitPushdown hd μ (-r) = unitPushdown hd μ r) :
    exactConductorEnergy d μ = 0 := by
  classical
  rw [exactConductorEnergy_eq_primitiveSourceEnergy hd (NeZero.pos d)]
  unfold primitiveSourceEnergy
  apply Finset.sum_eq_zero
  intro χ hχ
  have hodd := (Finset.mem_filter.mp hχ).2.2
  rw [← boundaryFlux_unitPushdown hd μ χ,
    boundaryFlux_even_zero (unitPushdown hd μ) hμ χ hodd]
  simp

theorem exactConductorEnergy_zero_of_zero_pushdown {m d : ℕ} [NeZero m] [NeZero d]
    (hd : d ∣ m) (μ : UnitClass m → ℂ) (hμ : ∀ r, unitPushdown hd μ r = 0) :
    exactConductorEnergy d μ = 0 :=
  exactConductorEnergy_zero_of_even_pushdown hd μ (fun r => (hμ (-r)).trans (hμ r).symm)

/-- At one level, vanishing of every primitive odd coefficient is the exact condition. -/
theorem exactConductorEnergy_zero_iff_primitive_odd_flux_zero
    {m d : ℕ} [NeZero m] [NeZero d] (hd : d ∣ m) (μ : UnitClass m → ℂ) :
    exactConductorEnergy d μ = 0 ↔
      ∀ χ : Character d, χ.IsPrimitive → χ.Odd → boundaryFlux (unitPushdown hd μ) χ = 0 := by
  classical
  rw [exactConductorEnergy_eq_primitiveSourceEnergy hd (NeZero.pos d)]
  unfold primitiveSourceEnergy
  simp_rw [← boundaryFlux_unitPushdown hd μ]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, sq_eq_zero_iff, norm_eq_zero]

end NField.Alignment.PushdownParity
