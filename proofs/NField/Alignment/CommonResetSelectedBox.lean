/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBoxArithmetic
import NField.Alignment.CommonResetConductorSelection

/-! # The actual complete inverse-frequency box with interval restrictions -/

noncomputable section

namespace NField.Alignment.CommonResetSelectedBox

open scoped BigOperators
open CommonResetConductorSelection CommonResetRetainedBands CommonResetBandWeighted
open CommonResetBoxArithmetic CommonResetSmallConductors

def selectedBox (p V J : ℕ) (S : ℕ → ℕ → ℕ → ℕ → Finset ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
    (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, ∑ u ∈ Finset.Icc 1 p,
      ∑ t ∈ conductorSelection p m u v j (quarterCutoff p) (S m u v j), originalFrequency p t u v j)

/-- Title: `The actual complete inverse-frequency box has a finite bound with every harmonic lift retained`. -/
theorem selected_box_finite_bound {p V J : ℕ} (hp : p.Prime) (hV : V ≤ p) (hJ : J ≤ p)
    (S : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (hS : ∀ m u v j, ∀ i ∈ S m u v j, ∀ k ∈ S m u v j, ∀ t, i≤t → t≤k → t∈S m u v j) :
    |selectedBox p V J S| ≤ 291600*boxConstant*boxArithmeticCost p*
      ((p : ℝ)*Real.sqrt (p : ℝ))*(Real.sqrt ((J : ℝ)*V)+1) := by
  have htri : |selectedBox p V J S| ≤
      ∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
        (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, ∑ u ∈ Finset.Icc 1 p,
          291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) := by
    unfold selectedBox
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro m hm
    rw [abs_mul, abs_of_nonneg (harmonic_nonneg m)]
    apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg _)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro v hv
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro u hu
    exact selected_band_bound_all_u hp (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hu).1
      (Finset.mem_Icc.mp hv).1 (Finset.mem_Icc.mp hj).1 (S m u v j) (hS m u v j)
  calc
    _ ≤ _ := htri
    _ = 291600*(∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
        (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, ∑ u ∈ Finset.Icc 1 p,
          (u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j)) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ 291600*(boxConstant*boxArithmeticCost p*((p : ℝ)*Real.sqrt (p : ℝ))*(Real.sqrt ((J : ℝ)*V)+1)) :=
      mul_le_mul_of_nonneg_left (full_box_majorant hp.one_le hV hJ) (by norm_num)
    _ = _ := by ring

/-- Title: `The full inverse-frequency box has the published three-halves-plus-epsilon bound`. -/
theorem selected_box_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p V J : ℕ, p.Prime → V ≤ p → J ≤ p →
      ∀ S : ℕ → ℕ → ℕ → ℕ → Finset ℕ,
      (∀ m u v j, ∀ i ∈ S m u v j, ∀ k ∈ S m u v j, ∀ t, i≤t → t≤k → t∈S m u v j) →
      |selectedBox p V J S| ≤ C*(p : ℝ)^(3/2+ε)*(Real.sqrt ((J : ℝ)*V)+1) := by
  obtain ⟨D, hD, hd⟩ := box_arithmetic_small_power ε hε
  refine ⟨291600*boxConstant*D, by have := boxConstant_pos; positivity, ?_⟩
  intro p V J hp hV hJ S hS
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hB := boxConstant_pos
  calc
    _ ≤ 291600*boxConstant*boxArithmeticCost p*((p : ℝ)*Real.sqrt (p : ℝ))*(Real.sqrt ((J : ℝ)*V)+1) :=
      selected_box_finite_bound hp hV hJ S hS
    _ ≤ 291600*boxConstant*(D*(p : ℝ)^ε)*((p : ℝ)*Real.sqrt (p : ℝ))*(Real.sqrt ((J : ℝ)*V)+1) := by
      gcongr
      exact hd p hp.one_le
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      have he : (p : ℝ)^ε*((p : ℝ)*(p : ℝ)^(1/2 : ℝ)) = (p : ℝ)^(3/2+ε) := by
        calc
          _ = (p : ℝ)^ε*((p : ℝ)^(1 : ℝ)*(p : ℝ)^(1/2 : ℝ)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hpR, ← Real.rpow_add hpR]; congr 1; ring
      calc
        _ = (291600*boxConstant*D)*((p : ℝ)^ε*((p : ℝ)*(p : ℝ)^(1/2 : ℝ)))*(Real.sqrt ((J : ℝ)*V)+1) := by ring
        _ = _ := by rw [he]

end NField.Alignment.CommonResetSelectedBox
