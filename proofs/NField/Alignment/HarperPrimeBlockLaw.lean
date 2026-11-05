/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlocks

/-!
# Actual logarithmic increments on the source prime blocks

The literal Euler products are nonzero and their real log norms equal
the previously formalized prime sums. All distinct source blocks are
jointly independent under the actual critical weighted law, with arbitrary
frequencies and injective reindexing. The quantitative characteristic
comparison is instantiated at the exact lower endpoint. An interval law
and the subsequent probability barrier are not asserted here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockLaw
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory SteinhausMoment HarperPrimeBlocks
  HarperEulerIntegral HarperEulerLogComparison HarperLocalExponentialMoment
  HarperTiltedMeasure HarperTiltedCoordinates HarperTiltedLogBounds
  HarperCharacteristicTaylor HarperWeightedCharacteristic HarperPrimeRangeCharacteristic
  HarperCharacteristicTail

def blockProduct (x : ℝ) (l : ℕ) (t : ℝ) (ω : PhaseSpace) : ℂ :=
  ∏ q ∈ primeBlock x l, (1-primeTerm q t ω)⁻¹
def blockLog (x : ℝ) (l : ℕ) (t : ℝ) (ω : PhaseSpace) : ℝ :=
  Real.log ‖blockProduct x l t ω‖
def blockCharacteristic (x : ℝ) (l : ℕ) (t u : ℝ) : ℂ :=
  ∫ ω, phaseExponential u (blockLog x l t ω)
    ∂tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)

theorem blockProduct_ne_zero (x : ℝ) (l : ℕ) (t : ℝ) (ω : PhaseSpace) :
    blockProduct x l t ω ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hq =>
    inv_ne_zero (localFactor_ne_zero (primeBlock_mem.mp hq).1 t ω))

theorem blockProduct_measurable (x : ℝ) (l : ℕ) (t : ℝ) :
    Measurable (blockProduct x l t) :=
  Finset.measurable_prod _ (fun q _ => (measurable_const.sub (primeTerm_measurable q t)).inv)

theorem blockLog_eq_rangeLog (x : ℝ) (l : ℕ) (t : ℝ) (ω : PhaseSpace) :
    blockLog x l t ω = rangeLog (primeBlock x l) (fun _ => t) ω := by
  unfold blockLog blockProduct rangeLog primeLog logFactor
  rw [norm_prod, Real.log_prod (fun q hq => norm_ne_zero_iff.mpr
    (inv_ne_zero (localFactor_ne_zero (primeBlock_mem.mp hq).1 t ω)))]

theorem blockLog_measurable (x : ℝ) (l : ℕ) (t : ℝ) :
    Measurable (blockLog x l t) := (blockProduct_measurable x l t).norm.log

theorem blockProducts_independent {ι : Type*} {x : ℝ} (hx : 1 ≤ x)
    (indices : ι → ℕ) (hi : Function.Injective indices) (t : ι → ℝ) :
    iIndepFun (fun i => blockProduct x (indices i) (t i))
      (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)) := by
  classical
  let f : (i : ι) → (primeBlock x (indices i) → UnitAddCircle) → ℂ := fun i z =>
    ∏ q : primeBlock x (indices i),
      (1-fourier 1 (z q)/(q.val : ℂ)^(linePoint (1/2) (t i)))⁻¹
  have hf (i : ι) : Measurable (f i) := Finset.measurable_prod _ (fun q _ =>
    (measurable_const.sub (((fourier 1).continuous.measurable.comp
      (measurable_pi_apply q)).div_const _)).inv)
  have hST : Pairwise (fun i j => Disjoint (primeBlock x (indices i))
      (primeBlock x (indices j))) := fun _ _ h =>
    primeBlock_pairwise_disjoint hx (fun he => h (hi he))
  have h := block_functions_independent (sourceCutoff x)
    (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
    (fun i => primeBlock x (indices i)) hST f hf
  have he : (fun i => blockProduct x (indices i) (t i)) =
      (fun i (ω : PhaseSpace) => f i ((primeBlock x (indices i)).restrict ω)) := by
    funext i ω
    unfold blockProduct
    rw [← (primeBlock x (indices i)).prod_coe_sort
      (fun q => (1-primeTerm q (t i) ω)⁻¹)]
    apply Finset.prod_congr rfl
    intro q _
    simp only [primeTerm, steinhaus_prime (primeBlock_mem.mp q.property).1]
    rfl
  rw [he]
  exact h

theorem blockLogs_independent {ι : Type*} {x : ℝ} (hx : 1 ≤ x)
    (indices : ι → ℕ) (hi : Function.Injective indices) (t : ι → ℝ) :
    iIndepFun (fun i => blockLog x (indices i) (t i))
      (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)) :=
  (blockProducts_independent hx indices hi t).comp
    (fun _ z => Real.log ‖z‖) (fun _ => measurable_id.norm.log)

theorem blockLogs_strictAnti_independent {ι : Type*} [LinearOrder ι]
    {x : ℝ} (hx : 1 ≤ x) (indices : ι → ℕ) (hi : StrictAnti indices) (t : ι → ℝ) :
    iIndepFun (fun i => blockLog x (indices i) (t i))
      (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)) :=
  blockLogs_independent hx indices hi.injective t

theorem blockCharacteristic_eq_range (x : ℝ) (l : ℕ) (t u : ℝ) :
    blockCharacteristic x l t u =
      rangeCharacteristic (sourceCutoff x) (primeBlock x l) (fun _ => t) u := by
  unfold blockCharacteristic rangeCharacteristic
  simp_rw [blockLog_eq_rangeLog]

theorem blockCharacteristic_gaussian_error {x : ℝ} (hx : 1 ≤ x) (l : ℕ)
    (hY : 2 ≤ blockLower x l) (t : ℝ) {u : ℝ} (hu : |u| ≤ Real.sqrt (blockLower x l)) :
    ‖blockCharacteristic x l t u-rangeGaussian (primeBlock x l) (fun _ => t) u‖ ≤
      4*comparisonConstant*(|u|+|u|^3)*(blockLower x l)^(-(1/2 : ℝ)) := by
  rw [blockCharacteristic_eq_range]
  exact rangeCharacteristic_cutoff_error (sourceCutoff x) hY _ (primeBlock_subset hx l)
    (fun _ hq => (primeBlock_mem.mp hq).2.1) _ hu

end NField.Alignment.HarperPrimeBlockLaw
