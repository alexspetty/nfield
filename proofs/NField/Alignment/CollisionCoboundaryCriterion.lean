/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionGeneralForcing
import NField.Alignment.CollisionFiniteAntiderivative

/-!
# The full positive-weight coboundary criterion

A continuous finite antiderivative tests the actual L1 forcing. It forces
all remainder pairings of any L2 solution. Positivity of the remainder
Gram matrix then bounds every finite age norm by the solution norm.
This proves necessity without assuming a Fourier expansion of the solution.
-/

noncomputable section

namespace NField.Alignment.CollisionCoboundaryCriterion

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialCoboundary CollisionL1Testing CollisionGeneralForcing
open CollisionFiniteAntiderivative CollisionGeneralWeightCriterion CollisionPotentialRecovery

theorem limiting_potential_forcing (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) (Y : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y)) :
    lowerL2 (Y - shift (-1) Y) = forcingL1 v := by
  have ht := hY.sub (((shift (-1)).continuous.tendsto Y).comp hY)
  have hl := (lowerL2.continuous.tendsto (Y-shift (-1) Y)).comp ht
  simp only [Function.comp_def, ← finiteForcing_eq_lower_difference] at hl
  exact tendsto_nhds_unique hl (finiteForcing_tendsto v hv h0 h1 hs)

theorem forcing_remainder_pairing_tendsto (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) (Y : HaarL2)
    (hY : lowerL2 (Y-shift (-1) Y) = forcingL1 v) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun M => inner ℝ (finitePotential v M) (remainderVector k)) atTop
      (nhds (inner ℝ Y (remainderVector k))) := by
  have h := ((continuousTest (antiderivativeMap k)).continuous.tendsto (forcingL1 v)).comp
    (finiteForcing_tendsto v hv h0 h1 hs)
  have htest (Z : HaarL2) :
      continuousTest (antiderivativeMap k) (lowerL2 (Z-shift (-1) Z)) =
        inner ℝ Z (remainderVector k) := by
    rw [continuousTest_lowerL2]
    exact backward_difference_pairing Z hk
  simpa only [Function.comp_def, finiteForcing_eq_lower_difference, ← hY, htest] using h

theorem inner_finitePotential (Y : HaarL2) (v : ℕ → ℝ) (M : ℕ) :
    inner ℝ Y (finitePotential v M) =
      (2/3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * inner ℝ Y (remainderVector k) := by
  simp only [finitePotential, inner_smul_right, inner_sum]

theorem forcing_finite_pairing_tendsto (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) (Y : HaarL2)
    (hY : lowerL2 (Y-shift (-1) Y) = forcingL1 v) (M : ℕ) :
    Tendsto (fun N => inner ℝ (finitePotential v N) (finitePotential v M)) atTop
      (nhds (inner ℝ Y (finitePotential v M))) := by
  simp_rw [inner_finitePotential]
  apply Filter.Tendsto.const_mul
  apply tendsto_finsetSum
  intro k hk
  exact (forcing_remainder_pairing_tendsto v hv h0 h1 hs Y hY
    (by have := (Finset.mem_Icc.mp hk).1; omega)).const_mul (v k)

theorem finite_age_inner_lower (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) {M N : ℕ} (hMN : M ≤ N) :
    ‖finitePotential v M‖^2 ≤ inner ℝ (finitePotential v N) (finitePotential v M) := by
  have hj (j : ℕ) : 0 ≤ inner ℝ (finitePotential v M) (ageVector v j) := by
    rw [← ageVector_partial_sum v h0 h1, sum_inner]
    exact Finset.sum_nonneg (fun i _ => ageVector_gram_nonneg v hv h0 i j)
  calc
    _ = inner ℝ (finitePotential v M) (finitePotential v M) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ j ∈ Finset.range (M+1), inner ℝ (finitePotential v M) (ageVector v j) := by
      rw [← inner_sum, ageVector_partial_sum v h0 h1]
    _ ≤ ∑ j ∈ Finset.range (N+1), inner ℝ (finitePotential v M) (ageVector v j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => hj j)
    _ = _ := by
      rw [← inner_sum, ageVector_partial_sum v h0 h1, real_inner_comm]

theorem forcing_finite_norm_bound (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) (Y : HaarL2)
    (hY : lowerL2 (Y-shift (-1) Y) = forcingL1 v) (M : ℕ) :
    ‖finitePotential v M‖^2 ≤ ‖Y‖^2 := by
  have hlow : ‖finitePotential v M‖^2 ≤ inner ℝ Y (finitePotential v M) := by
    apply ge_of_tendsto (forcing_finite_pairing_tendsto v hv h0 h1 hs Y hY M)
    filter_upwards [eventually_ge_atTop M] with N hN
    exact finite_age_inner_lower v hv h0 h1 hN
  have hupper := real_inner_le_norm Y (finitePotential v M)
  nlinarith [norm_nonneg Y, norm_nonneg (finitePotential v M)]

theorem energy_of_coboundary (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) (Y : HaarL2)
    (hY : lowerL2 (Y-shift (-1) Y) = forcingL1 v) : Summable (generalEnergy v) := by
  have hb : BddAbove (Set.range (fun n => ‖∑ k ∈ Finset.range n, ageVector v k‖^2)) := by
    refine ⟨‖Y‖^2, ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => simp
    | succ M =>
      change ‖∑ k ∈ Finset.range (M+1), ageVector v k‖^2 ≤ ‖Y‖^2
      rw [ageVector_partial_sum v h0 h1]
      exact forcing_finite_norm_bound v hv h0 h1 hs Y hY M
  obtain ⟨Z, hZ⟩ := (positive_gram_converges_iff_bounded (ageVector v)
    (ageVector_gram_nonneg v hv h0)).mpr hb
  have ht : Tendsto (finitePotential v) atTop (nhds Z) := by
    simpa only [Function.comp_def, ageVector_partial_sum v h0 h1] using
      hZ.comp (tendsto_add_atTop_nat 1)
  exact (generalEnergy_hasSum_of_limit v hv h0 h1 hs.summable Z ht).summable

theorem coboundary_energy_iff (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) :
    (∃ Y : HaarL2, (∫ x, Y x ∂phaseHaar) = 0 ∧
      lowerL2 (Y-shift (-1) Y) = forcingL1 v) ↔ Summable (generalEnergy v) := by
  constructor
  · rintro ⟨Y, _, hY⟩
    exact energy_of_coboundary v hv h0 h1 hs Y hY
  · intro he
    obtain ⟨Y, hY⟩ := (general_weights_converge_iff v hv h0 h1 hs.summable).mpr he
    exact ⟨Y, limiting_potential_mean_zero v Y hY, limiting_potential_forcing v hv h0 h1 hs Y hY⟩

theorem lower_difference_coe (Y : HaarL2) :
    (fun x => lowerL2 (Y-shift (-1) Y) x) =ᵐ[phaseHaar]
      (fun x => Y x - Y (translate (-1) x)) := by
  filter_upwards [Lp.coeFn_sub Y (shift (-1) Y), shift_coe (-1) Y] with x hsub hshift
  simp only [Pi.sub_apply] at hsub
  rw [lowerL2_coe, hsub, hshift]

theorem forcing_equation_iff_ae (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (hs : Summable v) (Y : HaarL2) :
    lowerL2 (Y-shift (-1) Y) = forcingL1 v ↔
      (fun x => Y x - Y (translate (-1) x)) =ᵐ[phaseHaar] forcingFunction v := by
  constructor
  · intro he
    exact (lower_difference_coe Y).symm.trans (he ▸ forcingL1_coe v hv h0 hs)
  · intro he
    apply Lp.ext
    exact (lower_difference_coe Y).trans (he.trans (forcingL1_coe v hv h0 hs).symm)

theorem general_weight_criterion (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) :
    ((∃ Y : HaarL2, Tendsto (finitePotential v) atTop (nhds Y)) ↔
      Summable (generalEnergy v)) ∧
    ((∃ Y : HaarL2, (∫ x, Y x ∂phaseHaar) = 0 ∧
      (fun x => Y x - Y (translate (-1) x)) =ᵐ[phaseHaar] forcingFunction v) ↔
      Summable (generalEnergy v)) := by
  refine ⟨general_weights_converge_iff v hv h0 h1 hs.summable, ?_⟩
  simp_rw [← forcing_equation_iff_ae v hv h0 hs.summable]
  exact coboundary_energy_iff v hv h0 h1 hs

end NField.Alignment.CollisionCoboundaryCriterion
