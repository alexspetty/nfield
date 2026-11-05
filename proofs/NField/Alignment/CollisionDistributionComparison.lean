/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialConcentration

/-!
# Distribution functions from concentration and square error

Both comparisons use the target observable's interval probabilities. No
density, independence or continuity of a distribution function is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDistributionComparison

open scoped Classical
open MeasureTheory

theorem distribution_upper_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (u ε : ℝ) :
    μ.real {x | X x ≤ u} ≤ μ.real {x | Y x ≤ u}+
      μ.real {x | Y x∈Set.Icc u (u+ε)}+μ.real {x | ε ≤ |X x-Y x|} := by
  have hsub : {x | X x ≤ u}⊆({x | Y x ≤ u} ∪ {x | Y x∈Set.Icc u (u+ε)}) ∪
      {x | ε ≤ |X x-Y x|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_cases he : ε ≤ |X x-Y x|
    · exact Or.inr he
    by_cases hy : Y x ≤ u
    · exact Or.inl (Or.inl hy)
    refine Or.inl (Or.inr ⟨(lt_of_not_ge hy).le,?_⟩)
    have ha := abs_lt.mp (lt_of_not_ge he)
    linarith [ha.1]
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _) le_rfl))

theorem distribution_lower_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (u ε : ℝ) :
    μ.real {x | Y x ≤ u} ≤ μ.real {x | X x ≤ u}+
      μ.real {x | Y x∈Set.Icc (u-ε) u}+μ.real {x | ε ≤ |X x-Y x|} := by
  have hsub : {x | Y x ≤ u}⊆({x | X x ≤ u} ∪ {x | Y x∈Set.Icc (u-ε) u}) ∪
      {x | ε ≤ |X x-Y x|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_cases he : ε ≤ |X x-Y x|
    · exact Or.inr he
    by_cases hy : X x ≤ u
    · exact Or.inl (Or.inl hy)
    refine Or.inl (Or.inr ⟨?_,hx⟩)
    have ha := abs_lt.mp (lt_of_not_ge he)
    have hh := lt_of_not_ge hy
    linarith [ha.2]
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _) le_rfl))

theorem square_error_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hXY : Integrable (fun x => (X x-Y x)^2) μ) :
    μ.real {x | ε ≤ |X x-Y x|} ≤ (∫ x, (X x-Y x)^2 ∂μ)/ε^2 := by
  have he : {x | ε ≤ |X x-Y x|}={x | ε^2 ≤ (X x-Y x)^2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      nlinarith [sq_abs (X x-Y x)]
    · intro h
      nlinarith [sq_abs (X x-Y x),abs_nonneg (X x-Y x)]
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg (X x-Y x))) hXY (ε^2)

theorem distribution_smoothing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {ε Q : ℝ} (hε : 0 < ε)
    (hXY : Integrable (fun x => (X x-Y x)^2) μ)
    (hQ : ∀ u : ℝ, μ.real {x | Y x∈Set.Icc u (u+ε)} ≤ Q) (u : ℝ) :
    |μ.real {x | X x ≤ u}-μ.real {x | Y x ≤ u}| ≤ Q+(∫ x, (X x-Y x)^2 ∂μ)/ε^2 := by
  have hu := distribution_upper_comparison μ X Y u ε
  have hl := distribution_lower_comparison μ X Y u ε
  have hq1 := hQ u
  have hq2 := hQ (u-ε)
  simp only [sub_add_cancel] at hq2
  have herr := square_error_probability μ X Y hε hXY
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem distribution_difference_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (u : ℝ) :
    |μ.real {x | X x ≤ u}-μ.real {x | Y x ≤ u}| ≤ 1 := by
  have hx : μ.real {x | X x ≤ u} ≤ 1 := measureReal_le_one
  have hy : μ.real {x | Y x ≤ u} ≤ 1 := measureReal_le_one
  have hx0 : 0 ≤ μ.real {x | X x ≤ u} := measureReal_nonneg
  have hy0 : 0 ≤ μ.real {x | Y x ≤ u} := measureReal_nonneg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem balance_quarter_powers {s : ℝ} (hs : 0 < s) :
    (s^(4/(9 : ℝ)))^(1/(4 : ℝ))=s^(1/(9 : ℝ)) ∧
    s/(s^(4/(9 : ℝ)))^2=s^(1/(9 : ℝ)) := by
  constructor
  · rw [← Real.rpow_mul hs.le]
    norm_num
  · have he : (s^(4/(9 : ℝ)))^2*s^(1/(9 : ℝ))=s := by
      rw [← Real.rpow_mul_natCast hs.le,← Real.rpow_add hs]
      norm_num
    apply (div_eq_iff (pow_ne_zero 2 (Real.rpow_pos_of_pos hs _).ne')).mpr
    simpa only [mul_comm] using he.symm

theorem distribution_ninth_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {C B s : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hs : 0 < s)
    (hXY : Integrable (fun x => (X x-Y x)^2) μ)
    (hE : (∫ x, (X x-Y x)^2 ∂μ) ≤ B*s)
    (hQ : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : ℝ,
      μ.real {x | Y x∈Set.Icc u (u+ε)} ≤ C*ε^(1/(4 : ℝ))) (u : ℝ) :
    |μ.real {x | X x ≤ u}-μ.real {x | Y x ≤ u}| ≤ (C+B+1)*s^(1/(9 : ℝ)) := by
  have hp : 0 ≤ s^(1/(9 : ℝ)) := Real.rpow_nonneg hs.le _
  by_cases hs1 : s ≤ 1
  · have hε : 0 < s^(4/(9 : ℝ)) := Real.rpow_pos_of_pos hs _
    have hε1 : s^(4/(9 : ℝ)) ≤ 1 := Real.rpow_le_one hs.le hs1 (by norm_num)
    have h := distribution_smoothing μ X Y hε hXY (hQ _ hε hε1) u
    have hE' := div_le_div_of_nonneg_right hE (sq_nonneg (s^(4/(9 : ℝ))))
    have he := balance_quarter_powers hs
    rw [mul_div_assoc,he.2] at hE'
    rw [he.1] at h
    nlinarith
  · have hlarge : 1 ≤ s^(1/(9 : ℝ)) := Real.one_le_rpow (le_of_not_ge hs1) (by norm_num)
    have hK : 1 ≤ C+B+1 := by linarith
    exact (distribution_difference_le_one μ X Y u).trans
      (hlarge.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hp))

end NField.Alignment.CollisionDistributionComparison
