/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperUnconditioningScales

/-!
# Frequency shifts in the actual Haar phase model

Coordinate translation preserves the original infinite product of circle
Haar measures. Its action on prime values gives the literal vertical shift
of the finite Euler product, hence equality of the original fractional grid
moments at every real center. No low-moment upper bound is assumed here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPhaseShift
open scoped BigOperators Topology
open MeasureTheory SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerIncrement HarperEulerSecondMoment HarperEulerGridComparison HarperUnconditioning
  HarperUnconditioningScales HarperFrequencyIntervals HarperFrequencyTail
  HarperConditioningFrequencies HarperRoundedCutoff CollisionMertensInput

def shiftCoordinate (v : ℝ) (q : ℕ) : UnitAddCircle :=
  ((-v*Real.log (q : ℝ)/(2*Real.pi) : ℝ) : UnitAddCircle)

def phaseShift (v : ℝ) : PhaseSpace ≃ᵐ PhaseSpace :=
  MeasurableEquiv.addLeft (shiftCoordinate v)

theorem phaseShift_apply (v : ℝ) (ω : PhaseSpace) (q : ℕ) :
    phaseShift v ω q = shiftCoordinate v q+ω q := rfl

theorem phaseShift_measurePreserving (v : ℝ) :
    MeasurePreserving (phaseShift v) phaseMeasure phaseMeasure := by
  refine ⟨(phaseShift v).measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => AddCircle.haarAddCircle)).map
    (fun ω q => shiftCoordinate v q+ω q) = _
  rw [Measure.infinitePi_map_pi _
    (f := fun q (z : UnitAddCircle) => shiftCoordinate v q+z)
    (fun q => (MeasurableEquiv.addLeft (shiftCoordinate v q)).measurable)]
  simp only [map_add_left_eq_self]
  rfl

theorem phaseShift_integral (v : ℝ) (f : PhaseSpace → ℝ) :
    (∫ ω, f (phaseShift v ω) ∂phaseMeasure) = ∫ ω, f ω ∂phaseMeasure :=
  (phaseShift_measurePreserving v).integral_comp' f

theorem fourier_shiftCoordinate {q : ℕ} (hq : q ≠ 0) (v : ℝ) :
    fourier 1 (shiftCoordinate v q) = twist q v := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hlog : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  unfold shiftCoordinate twist
  rw [fourier_coe_apply, Complex.cpow_def_of_ne_zero hqC, hlog]
  congr 1
  push_cast
  field_simp

theorem phase_one_shift {q : ℕ} (hq : q ≠ 0) (v : ℝ) (ω : PhaseSpace) :
    phase q 1 (phaseShift v ω) = twist q v*phase q 1 ω := by
  change fourier 1 (shiftCoordinate v q+ω q) = _
  rw [fourier_one, AddCircle.toCircle_add, Circle.coe_mul, ← fourier_one,
    fourier_shiftCoordinate hq]
  simp only [phase, fourier_one]

theorem steinhaus_prime_shift {q : ℕ} (hq : q.Prime) (v : ℝ) (ω : PhaseSpace) :
    steinhaus q (phaseShift v ω) = twist q v*steinhaus q ω := by
  rw [steinhaus_prime hq, steinhaus_prime hq, phase_one_shift hq.ne_zero]

theorem eulerProduct_shift (P σ t v : ℝ) (ω : PhaseSpace) :
    eulerProduct P (linePoint σ t) (phaseShift v ω) =
      eulerProduct P (linePoint σ (t+v)) ω := by
  unfold eulerProduct
  apply Finset.prod_congr rfl
  intro q hq
  have hprime := (primesUpTo_mem.mp hq).1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rw [steinhaus_prime_shift hprime]
  have he : -linePoint σ (t+v) = (-(v : ℂ)*Complex.I)+(-linePoint σ t) := by
    simp only [linePoint, Complex.ofReal_add]
    ring
  simp only [div_eq_mul_inv, ← Complex.cpow_neg, he, Complex.cpow_add _ _ hqC, twist]
  ring

theorem intervalEnergy_shift (P σ v : ℝ) {a b : ℝ} (hab : a ≤ b) (ω : PhaseSpace) :
    intervalEnergy P σ a b (phaseShift v ω) = intervalEnergy P σ (a+v) (b+v) ω := by
  unfold intervalEnergy
  have he := intervalIntegral.integral_comp_add_right
    (fun t => verticalEnergy P σ (t,ω)) v (a := a) (b := b)
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (show a+v ≤ b+v by linarith)] at he
  calc
    _ = ∫ t in Set.Ioc a b, verticalEnergy P σ (t+v,ω) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        simp only [verticalEnergy, eulerProduct_shift])
    _ = _ := he

theorem intervalFractionalMoment_shift (P σ r v : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ ω, (intervalEnergy P σ (a+v) (b+v) ω)^r ∂phaseMeasure) =
      ∫ ω, (intervalEnergy P σ a b ω)^r ∂phaseMeasure := by
  simp_rw [← intervalEnergy_shift P σ v hab]
  exact phaseShift_integral v (fun ω => (intervalEnergy P σ a b ω)^r)

theorem discreteEnergy_shift (P t v : ℝ) (ω : PhaseSpace) :
    discreteEnergy P t (phaseShift v ω) = discreteEnergy P (t+v) ω := by
  unfold discreteEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [eulerProduct_shift,
    show t+(k : ℝ)/HarperEulerDiscretization.gridScale P+v =
      (t+v)+(k : ℝ)/HarperEulerDiscretization.gridScale P by ring]

theorem unconditionalGridMoment_add (P t v : ℝ) :
    unconditionalGridMoment P (t+v) = unconditionalGridMoment P t := by
  unfold unconditionalGridMoment
  simp_rw [← discreteEnergy_shift P t v]
  exact phaseShift_integral v (fun ω => (discreteEnergy P t ω)^(3/4 : ℝ))

theorem unconditionalGridMoment_eq_zero (P v : ℝ) :
    unconditionalGridMoment P v = unconditionalGridMoment P 0 := by
  simpa only [zero_add] using unconditionalGridMoment_add P 0 v

theorem unconditionalCentralMoment_eq (p : ℕ) :
    unconditionalCentralMoment p =
      (∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
        frequencyWeight (3/2) v)*unconditionalGridMoment (primeCutoff ((p : ℝ)-1)) 0 := by
  unfold unconditionalCentralMoment
  conv_lhs =>
    enter [2, v]
    rw [unconditionalGridMoment_eq_zero]
  rw [Finset.sum_mul]

end NField.Alignment.HarperPhaseShift
