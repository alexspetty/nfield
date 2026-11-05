/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMomentNormBounds
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Convergence of the actual cutoffs in every finite Lr

The higher norm bound supplies uniform absolute continuity on small sets.
Vitali then upgrades the already proved L2 convergence in measure. The
finite continuous cutoff representatives are explicitly connected to the
L2 vectors before applying the convergence theorem.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialLpConvergence

open scoped Classical ENNReal
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionDistributionApproximation
open CollisionPotentialMoments CollisionMomentNormBounds

theorem small_set_norm_bound {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : I → Ω → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    {p q C : ℝ} (hp : 0 < p) (hpq : p < q)
    (hC : ∀ i, eLpNorm (F i) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C)
    (i : I) (s : Set Ω) (hs : MeasurableSet s) :
    eLpNorm (s.indicator (F i)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C*(μ s)^(1/p-1/q) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
    (ENNReal.ofReal_le_ofReal hpq.le) (hF i).restrict
  rw [ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal (hp.trans hpq).le,
    Measure.restrict_apply_univ] at h
  exact h.trans (mul_le_mul_left ((eLpNorm_mono_measure (F i) Measure.restrict_le_self).trans (hC i)) _)

theorem higher_norm_uniform_integrability {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : I → Ω → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    {p q C : ℝ} (hp : 0 < p) (hpq : p < q) (hC : 0 < C)
    (hbound : ∀ i, eLpNorm (F i) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    UnifIntegrable F (ENNReal.ofReal p) μ := by
  intro ε hε
  let a : ℝ := 1/p-1/q
  have ha : 0 < a := sub_pos.mpr ((one_div_lt_one_div (hp.trans hpq) hp).mpr hpq)
  let δ : ℝ := (ε/C)^(1/a)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hε hC) _
  have hδa : δ^a=ε/C := by
    dsimp only [δ]
    rw [← Real.rpow_mul (div_pos hε hC).le]
    rw [one_div_mul_cancel ha.ne',Real.rpow_one]
  have he : ENNReal.ofReal C*(ENNReal.ofReal δ)^a=ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_rpow_of_nonneg hδ.le ha.le,← ENNReal.ofReal_mul hC.le,hδa]
    congr 1
    field_simp
  refine ⟨δ,hδ,fun i s hs hμs => ?_⟩
  calc
    _ ≤ ENNReal.ofReal C*(μ s)^a := small_set_norm_bound F hF hp hpq hbound i s hs
    _ ≤ ENNReal.ofReal C*(ENNReal.ofReal δ)^a :=
      mul_le_mul_right (ENNReal.rpow_le_rpow hμs ha.le) _
    _ = _ := he

theorem cutoff_uniform_integrability {r : ℝ} (hr : 1 ≤ r) :
    UnifIntegrable (fun M => (potentialMap collisionWeight M : Phase → ℝ))
      (ENNReal.ofReal r) phaseHaar := by
  obtain ⟨K,hK,hbound⟩ := potential_quadratic_norm_bound
  have hq : 1 ≤ r+1 := by linarith
  apply higher_norm_uniform_integrability
    (fun M => (potentialMap collisionWeight M : Phase → ℝ))
    (fun M => (potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable)
    (q := r+1) (C := K*(r+1)^2) (by linarith) (by linarith) (by positivity)
  intro M
  rw [← ofReal_lpNorm (cutoff_memLp_finite M (ENNReal.ofReal (r+1)) ENNReal.ofReal_ne_top)]
  exact ENNReal.ofReal_le_ofReal ((hbound (r+1) hq).2 M)

theorem cutoff_tendsto_in_measure :
    TendstoInMeasure phaseHaar (fun M => (potentialMap collisionWeight M : Phase → ℝ))
      atTop collisionPotential := by
  exact TendstoInMeasure.congr (fun M => finitePotential_coe_map M)
    Filter.EventuallyEq.rfl (tendstoInMeasure_of_tendsto_Lp tendsto_collisionPotential)

theorem cutoff_tendsto_eLpNorm {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun M => eLpNorm
      (fun x => potentialMap collisionWeight M x-collisionPotential x)
      (ENNReal.ofReal r) phaseHaar) atTop (nhds 0) := by
  apply tendsto_Lp_finite_of_tendstoInMeasure
    (by simpa using (ENNReal.ofReal_le_ofReal hr)) ENNReal.ofReal_ne_top
    (fun M => (potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable)
    (potential_memLp_finite _ ENNReal.ofReal_ne_top)
    (cutoff_uniform_integrability hr) cutoff_tendsto_in_measure

theorem cutoff_tendsto_lpNorm {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun M => lpNorm
      (fun x => potentialMap collisionWeight M x-collisionPotential x)
      (ENNReal.ofReal r) phaseHaar) atTop (nhds 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (cutoff_tendsto_eLpNorm hr)
  have he (M : ℕ) :
      (eLpNorm (fun x => potentialMap collisionWeight M x-collisionPotential x)
        (ENNReal.ofReal r) phaseHaar).toReal=
      lpNorm (fun x => potentialMap collisionWeight M x-collisionPotential x)
        (ENNReal.ofReal r) phaseHaar :=
    toReal_eLpNorm ((potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable collisionPotential))
  simpa only [Function.comp_def,ENNReal.toReal_zero,he] using h

end NField.Alignment.CollisionPotentialLpConvergence
