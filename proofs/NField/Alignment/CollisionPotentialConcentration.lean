/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReturnConcentration
import NField.Alignment.CollisionConcentrationScales
import NField.Alignment.CollisionPotentialAtomless

/-!
# One-quarter concentration of the actual collision potential

The stationary recurrence, unconditional prime-block estimate and literal
floor choices give the small-interval bound. A single universal constant
also covers the initial interval widths. No finite computation is used.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialConcentration

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialConvergence
open CollisionPotentialCoboundary CollisionResetIntegrability
open CollisionReturnConcentration CollisionConcentrationScales
open CollisionPotentialAtomless CollisionPrimeBlockAtomless
open CollisionReturnTimeMoments CollisionReturnPairCounting

theorem literal_stationary_recurrence : ∃ K : ℝ, 0<K ∧ ∀ ε : ℝ,
    0<ε → Real.exp 40≤1/ε → ∀ u : ℝ,
    let P : ℕ := ⌊Real.log (1/ε)/(10*ε)⌋₊
    let N : ℕ := ⌊(P : ℝ)/4⌋₊
    let A : Set Phase := potentialInterval u ε
    let R : ℝ := phaseHaar.real A/(N : ℝ)+2/(N : ℝ)^2*
      (∑ h∈Finset.Icc 1 (N-1), ((N : ℝ)-(h : ℝ))*
        phaseHaar.real (A ∩ CollisionPotentialCoboundary.translate (h : ℤ) ⁻¹' A))
    (phaseHaar.real A)^2≤R ∧ R≤K*Real.sqrt (Real.log P/(N : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := potential_return_bound
  refine ⟨1+4*C,by linarith,?_⟩
  intro ε hε ht u
  rw [← primeScale_reciprocal hε]
  dsimp only
  rw [← returnScale_floor]
  have hn := returnScale_pos ht
  have hw : 3*ε<Real.log ((primeScale (1/ε) : ℝ)/2)/(primeScale (1/ε) : ℝ) := by
    have h := primeScale_width ht
    have he : 3/(1/ε)=3*ε := by field_simp
    rwa [he] at h
  refine ⟨stationary_recurrence_Icc (potentialInterval_nullMeasurable u ε) hn,?_⟩
  have hb := recurrence_expression_root_bound (potentialInterval u ε) (by linarith : 0≤C)
    (primeScale_log_lower ht) hn (fun h hh hhN => hbound (primeScale (1/ε)) h hh
      (by have := returnScale_upper (1/ε); omega) u ε hw)
  simpa only [weightedGapSum_Icc,returnProbability] using hb

theorem double_sqrt_eq_quarter {ε : ℝ} (hε : 0≤ε) :
    Real.sqrt (Real.sqrt ε)=ε^(1/(4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hε]
  norm_num

theorem quarter_of_square_root_bound {ρ K ε : ℝ} (hρ : 0≤ρ) (hK : 0≤K) (hε : 0≤ε)
    (h : ρ^2≤K*Real.sqrt (320*ε)) :
    ρ≤(Real.sqrt K*Real.sqrt (Real.sqrt 320))*ε^(1/(4 : ℝ)) := by
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hρ,Real.sqrt_mul hK,
    Real.sqrt_mul (by norm_num : (0 : ℝ)≤320),
    Real.sqrt_mul (Real.sqrt_nonneg (320 : ℝ)),double_sqrt_eq_quarter hε] at hs
  simpa only [mul_assoc] using hs

theorem potential_concentration_small : ∃ D : ℝ, 0<D ∧ ∀ ε : ℝ,
    0<ε → Real.exp 40≤1/ε → ∀ u : ℝ,
      phaseHaar.real (potentialInterval u ε)≤D*ε^(1/(4 : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := potential_stationary_root_bound
  refine ⟨Real.sqrt K*Real.sqrt (Real.sqrt 320),by positivity,?_⟩
  intro ε hε ht u
  have hwidth : 3*ε<Real.log ((primeScale (1/ε) : ℝ)/2)/(primeScale (1/ε) : ℝ) := by
    have hw := primeScale_width ht
    have he : 3/(1/ε)=3*ε := by field_simp
    rwa [he] at hw
  have hb := hbound (primeScale (1/ε)) (returnScale (1/ε)) (returnScale_pos ht)
    (returnScale_upper (1/ε)) (primeScale_log_lower ht) u ε hwidth
  have hr : Real.log (primeScale (1/ε))/(returnScale (1/ε) : ℝ)≤320*ε := by
    have hr := scale_ratio_bound ht
    have he : 320/(1/ε)=320*ε := by field_simp
    rwa [he] at hr
  exact quarter_of_square_root_bound measureReal_nonneg hK.le hε.le
    (hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) hK.le))

theorem potential_interval_bound : ∃ C : ℝ, 0<C ∧ ∀ ε : ℝ,
    0<ε → ε≤1 → ∀ u : ℝ,
      phaseHaar.real (potentialInterval u ε)≤C*ε^(1/(4 : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := potential_concentration_small
  let C : ℝ := max D (Real.exp 40)
  have hC : 0<C := hD.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro ε hε hε1 u
  have hp : 0≤ε^(1/(4 : ℝ)) := Real.rpow_nonneg hε.le _
  by_cases ht : Real.exp 40≤1/ε
  · exact (hbound ε hε ht u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hprod : 1≤Real.exp 40*ε :=
      ((div_lt_iff₀ hε).mp (lt_of_not_ge ht)).le
    have hεp : ε≤ε^(1/(4 : ℝ)) := Real.self_le_rpow_of_le_one hε.le hε1 (by norm_num)
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ Real.exp 40*ε := hprod
      _ ≤ C*ε^(1/(4 : ℝ)) := mul_le_mul (le_max_right _ _) hεp hε.le hC.le

theorem potential_concentration : ∃ C : ℝ, 0<C ∧ ∀ ε : ℝ,
    0<ε → ε≤1 →
      (⨆ u : ℝ, phaseHaar.real {x | collisionPotential x∈Set.Icc u (u+ε)})≤C*ε^(1/(4 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := potential_interval_bound
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  exact ciSup_le (hbound ε hε hε1)

/-- All assertions of the manuscript's concentration and absence-of-atoms theorem. -/
theorem concentration_and_absence_of_atoms :
    (∃ C : ℝ, 0<C ∧ ∀ ε : ℝ, 0<ε → ε≤1 →
      (⨆ u : ℝ, phaseHaar.real {x | collisionPotential x∈Set.Icc u (u+ε)})≤C*ε^(1/(4 : ℝ))) ∧
    (∀ u : ℝ, phaseHaar {x | collisionPotential x=u}=0) ∧
    (∀ u : ℝ, phaseHaar {x | resetFunction x=u}=0) ∧
    (∀ u : ℝ, phaseHaar {x | increment x=u}=0) ∧
    (∀ h : ℕ, 0<h → ∀ u : ℝ, phaseHaar {x | blockFunction h x=u}=0) := by
  exact ⟨potential_concentration,potential_atom_measure_zero,resetFunction_atom_measure_zero,
    increment_atom_measure_zero,fun h hh u => incrementBlock_atom_measure_zero hh u⟩

end NField.Alignment.CollisionPotentialConcentration
