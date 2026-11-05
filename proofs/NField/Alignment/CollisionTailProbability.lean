/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTailBounds

/-!
# Chebyshev tail bounds with the exact stationary cutoff height

The same remainder controls the infinite potential and every finite
cutoff. All probabilities are on the actual profinite Haar space.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionTailProbability

open scoped Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialTailBounds
open CollisionDistributionComparison CollisionDistributionApproximation

theorem tail_of_bounded_approximation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {A H : ℝ}
    (hH : A < H) (hX : ∀ x, |X x| ≤ A)
    (hXY : Integrable (fun x => (X x-Y x)^2) μ) :
    μ.real {x | H < |Y x|} ≤ (∫ x, (X x-Y x)^2 ∂μ)/(H-A)^2 := by
  have hsub : {x | H < |Y x|} ⊆ {x | H-A ≤ |X x-Y x|} := by
    intro x hx
    change H < |Y x| at hx
    have ht : |Y x| ≤ |X x|+|X x-Y x| := by
      calc
        _ = |X x+(Y x-X x)| := by congr 1; ring
        _ ≤ |X x|+|Y x-X x| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm]
    have hb := hX x
    change H-A ≤ |X x-Y x|
    linarith
  exact (measureReal_mono hsub).trans
    (square_error_probability μ X Y (sub_pos.mpr hH) hXY)

theorem infinite_tail_chebyshev (L : ℕ) {H : ℝ}
    (hH : stationaryAge collisionWeight L < H) :
    phaseHaar.real {x | H < |collisionPotential x|} ≤
      ‖collisionPotential-finitePotential collisionWeight L‖^2/
        (H-stationaryAge collisionWeight L)^2 := by
  have h := tail_of_bounded_approximation phaseHaar (potentialMap collisionWeight L)
    collisionPotential hH (potentialMap_abs_bound L) (cutoff_error_sq_integrable L)
  rwa [cutoff_error_second_moment] at h

theorem finite_cutoff_error_coe (L M : ℕ) :
    (fun x => (finitePotential collisionWeight L-finitePotential collisionWeight M) x) =ᵐ[phaseHaar]
      (fun x => potentialMap collisionWeight L x-potentialMap collisionWeight M x) := by
  filter_upwards [Lp.coeFn_sub (finitePotential collisionWeight L) (finitePotential collisionWeight M),
    finitePotential_coe_map L,finitePotential_coe_map M] with x hx hL hM
  simp only [Pi.sub_apply] at hx
  rw [hx,hL,hM]

theorem finite_cutoff_error_sq_integrable (L M : ℕ) :
    Integrable (fun x => (potentialMap collisionWeight L x-potentialMap collisionWeight M x)^2)
      phaseHaar :=
  ((memLp_congr_ae (finite_cutoff_error_coe L M)).mp
    (Lp.memLp (finitePotential collisionWeight L-finitePotential collisionWeight M))).integrable_sq

theorem finite_cutoff_error_second_moment (L M : ℕ) :
    (∫ x, (potentialMap collisionWeight L x-potentialMap collisionWeight M x)^2 ∂phaseHaar)=
      ‖finitePotential collisionWeight M-finitePotential collisionWeight L‖^2 := by
  rw [norm_sub_rev,← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [finite_cutoff_error_coe L M] with x hx
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]

theorem finite_tail_chebyshev (L M : ℕ) {H : ℝ}
    (hH : stationaryAge collisionWeight L < H) :
    phaseHaar.real {x | H < |potentialMap collisionWeight M x|} ≤
      ‖collisionPotential-finitePotential collisionWeight L‖^2/
        (H-stationaryAge collisionWeight L)^2 := by
  by_cases hML : M ≤ L
  · have he : {x | H < |potentialMap collisionWeight M x|}=(∅ : Set Phase) := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      have hb := (potentialMap_abs_bound M x).trans (stationaryAge_monotone hML)
      linarith
    rw [he,measureReal_empty]
    positivity
  · have h := tail_of_bounded_approximation phaseHaar (potentialMap collisionWeight L)
      (potentialMap collisionWeight M) hH (potentialMap_abs_bound L)
      (finite_cutoff_error_sq_integrable L M)
    rw [finite_cutoff_error_second_moment] at h
    have hn := finite_cutoff_tail_norm_le_infinite (le_of_not_ge hML)
    have hs : ‖finitePotential collisionWeight M-finitePotential collisionWeight L‖^2 ≤
        ‖collisionPotential-finitePotential collisionWeight L‖^2 := by
      nlinarith [norm_nonneg (finitePotential collisionWeight M-finitePotential collisionWeight L),
        norm_nonneg (collisionPotential-finitePotential collisionWeight L)]
    exact h.trans (div_le_div_of_nonneg_right hs (sq_nonneg _))

theorem uniform_tail_variance_bound : ∃ B : ℝ, 0 < B ∧ ∀ L : ℕ, 1 ≤ L → ∀ H : ℝ,
    stationaryAge collisionWeight L < H →
    (phaseHaar.real {x | H < |collisionPotential x|} ≤
      B*distributionScale L/(H-stationaryAge collisionWeight L)^2) ∧
    (∀ M : ℕ, phaseHaar.real {x | H < |potentialMap collisionWeight M x|} ≤
      B*distributionScale L/(H-stationaryAge collisionWeight L)^2) := by
  obtain ⟨B,hB,hbound⟩ := cutoff_variance_uniform
  refine ⟨B,hB,?_⟩
  intro L hL H hH
  have hb := hbound L hL
  rw [cutoff_error_second_moment] at hb
  have hd := div_le_div_of_nonneg_right hb (sq_nonneg (H-stationaryAge collisionWeight L))
  exact ⟨(infinite_tail_chebyshev L hH).trans hd,
    fun M => (finite_tail_chebyshev L M hH).trans hd⟩

end NField.Alignment.CollisionTailProbability
