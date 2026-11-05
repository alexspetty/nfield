/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReturnTimeMoments
import NField.Alignment.CollisionRootSumBounds

/-!
# Quantitative recurrence from the proved forcing-block bound

This keeps the actual potential interval, its return intersection, and
the interval length 3 epsilon explicit. The final floor choices and the
one-quarter exponent are assembled separately.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionReturnConcentration

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialCoboundary
open CollisionPotentialConvergence CollisionActivationArithmetic
open CollisionReturnTimeMoments CollisionReturnPairCounting CollisionRootSumBounds
open CollisionDyadicBlockConcentration

def potentialInterval (u ε : ℝ) : Set Phase := {x | collisionPotential x∈Set.Icc u (u+ε)}

theorem potentialInterval_nullMeasurable (u ε : ℝ) :
    NullMeasurableSet (potentialInterval u ε) phaseHaar :=
  (Lp.aestronglyMeasurable collisionPotential).aemeasurable.nullMeasurable measurableSet_Icc

theorem potential_return_forcing (u ε : ℝ) (h : ℕ) :
    returnProbability (potentialInterval u ε) h≤
      phaseHaar.real {x | forcingBlock h x∈Set.Icc ((h : ℝ)-3*ε/2) ((h : ℝ)+3*ε/2)} := by
  have hsub : (potentialInterval u ε ∩ CollisionPotentialCoboundary.translate (h : ℤ) ⁻¹'
      potentialInterval u ε : Set Phase) ≤ᵐ[phaseHaar]
      ({x | forcingBlock h x∈Set.Icc ((h : ℝ)-3*ε/2) ((h : ℝ)+3*ε/2)} : Set Phase) := by
    filter_upwards [block_telescope_ae h] with x hx
    rintro ⟨hx0,hxh⟩
    change u≤collisionPotential x ∧ collisionPotential x≤u+ε at hx0
    change u≤collisionPotential (CollisionPotentialCoboundary.translate (h : ℤ) x) ∧
      collisionPotential (CollisionPotentialCoboundary.translate (h : ℤ) x)≤u+ε at hxh
    change (h : ℝ)-3*ε/2≤forcingBlock h x ∧ forcingBlock h x≤(h : ℝ)+3*ε/2
    rw [blockFunction_forcingBlock] at hx
    constructor <;> linarith [hx0.1,hx0.2,hxh.1,hxh.2]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

theorem potential_return_bound : ∃ C : ℝ, 1≤C ∧
    ∀ P h : ℕ, 0<h → 4*h≤P → ∀ u ε : ℝ,
      3*ε<Real.log ((P : ℝ)/2)/(P : ℝ) →
      returnProbability (potentialInterval u ε) h≤C*Real.sqrt (Real.log P/(h : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := dyadic_block_concentration_uniform
  refine ⟨C,hC,?_⟩
  intro P h hh hhP u ε hε
  exact (potential_return_forcing u ε h).trans
    (hbound P h hh hhP ((h : ℝ)-3*ε/2) ((h : ℝ)+3*ε/2) (by linarith))

theorem weightedGapSum_root_bound {a : ℕ → ℝ} {C L : ℝ} (hC : 0≤C) (hL : 0≤L)
    (N : ℕ) (ha : ∀ h : ℕ, 0<h → h≤N → a h≤C*Real.sqrt (L/(h : ℝ))) :
    weightedGapSum a N≤(N : ℝ)*C*(2*Real.sqrt L*Real.sqrt (N : ℝ)) := by
  calc
    _ ≤ ∑ k∈Finset.range N, (N : ℝ)*C*Real.sqrt (L/(k+1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k+1≤N := by have := Finset.mem_range.mp hk; omega
      calc
        _ ≤ ((N-(k+1) : ℕ) : ℝ)*(C*Real.sqrt (L/(k+1 : ℕ))) :=
          mul_le_mul_of_nonneg_left (ha (k+1) (by omega) hkN) (Nat.cast_nonneg _)
        _ ≤ (N : ℝ)*(C*Real.sqrt (L/(k+1 : ℕ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N (k+1))
            (mul_nonneg hC (Real.sqrt_nonneg _))
        _ = _ := by ring
    _ = (N : ℝ)*C*(∑ k∈Finset.range N, Real.sqrt (L/(k+1 : ℕ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_ratio_sum hL N)
      (mul_nonneg (Nat.cast_nonneg N) hC)

theorem recurrence_expression_root_bound (A : Set Phase)
    {C L : ℝ} (hC : 0≤C) (hL : 1≤L) {N : ℕ} (hN : 0<N)
    (ha : ∀ h : ℕ, 0<h → h≤N → returnProbability A h≤C*Real.sqrt (L/(h : ℝ))) :
    phaseHaar.real A/(N : ℝ)+2/(N : ℝ)^2*weightedGapSum (returnProbability A) N≤
      (1+4*C)*Real.sqrt (L/(N : ℝ)) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hl : 0≤L := by linarith
  have hw := weightedGapSum_root_bound hC hl N ha
  have hmass : phaseHaar.real A/(N : ℝ)≤1/(N : ℝ) :=
    div_le_div_of_nonneg_right measureReal_le_one hn.le
  have he : (2/(N : ℝ)^2)*((N : ℝ)*C*(2*Real.sqrt L*Real.sqrt (N : ℝ)))=
      4*C*Real.sqrt (L/(N : ℝ)) := by
    rw [Real.sqrt_div hl]
    have hs : Real.sqrt (N : ℝ)≠0 := (Real.sqrt_pos.mpr hn).ne'
    have hs2 := Real.sq_sqrt hn.le
    field_simp
    rw [hs2]
    ring
  have hmul := mul_le_mul_of_nonneg_left hw
    (show 0≤2/(N : ℝ)^2 by positivity)
  rw [he] at hmul
  have hsmall := reciprocal_le_sqrt_ratio hL hN
  nlinarith

theorem stationary_root_bound {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    {C L : ℝ} (hC : 0≤C) (hL : 1≤L) {N : ℕ} (hN : 0<N)
    (ha : ∀ h : ℕ, 0<h → h≤N → returnProbability A h≤C*Real.sqrt (L/(h : ℝ))) :
    (phaseHaar.real A)^2≤(1+4*C)*Real.sqrt (L/(N : ℝ)) :=
  (stationary_recurrence hA hN).trans (recurrence_expression_root_bound A hC hL hN ha)

theorem potential_stationary_root_bound : ∃ K : ℝ, 0<K ∧
    ∀ P N : ℕ, 0<N → 4*N≤P → 1≤Real.log P → ∀ u ε : ℝ,
      3*ε<Real.log ((P : ℝ)/2)/(P : ℝ) →
      (phaseHaar.real (potentialInterval u ε))^2≤K*Real.sqrt (Real.log P/(N : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := potential_return_bound
  refine ⟨1+4*C,by linarith,?_⟩
  intro P N hN hNP hP u ε hε
  exact stationary_root_bound (potentialInterval_nullMeasurable u ε) (by linarith) hP hN
    (fun h hh hhN => hbound P h hh (by omega) u ε hε)

end NField.Alignment.CollisionReturnConcentration
