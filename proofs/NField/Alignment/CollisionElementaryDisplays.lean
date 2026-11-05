/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.GcdLcmCapacity
import NField.Alignment.CollisionBoundaryTesting
import NField.Alignment.CollisionJointMoments
import NField.Alignment.CollisionConductorOne
import NField.Alignment.CollisionAmplitudeTail

/-!
# Literal capacity, reset, finite-value and amplitude displays

These statements reconcile supporting manuscript blocks with the actual
objects. In particular the reset series is asserted on its proved set of
absolute convergence, and the rational examples use the full integer reset.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionElementaryDisplays

open scoped BigOperators ENNReal Classical
open Filter MeasureTheory Asymptotics
open GcdLcmCapacity PrimeSquareCollisionWindow SecondaryCapacityLedger
open CollisionRemainderDynamics CollisionMassReadout CollisionResolutionLaw
open ProfiniteRemainderMeasure CollisionResetIntegrability CollisionPotentialCoboundary
open CollisionBoundaryTesting CollisionJointMoments CollisionCylinderMeans
open CollisionAmplitudeTail CollisionPositiveLogTail
open CollisionJordanVariance

theorem literal_capacity_and_deficit (N : ℕ) :
    continuousCapacity N=(1/3 : ℝ)*
      ∑ i : FirstWindowIndex (N+1), ∑ j : FirstWindowIndex (N+1),
        ((Nat.gcd (firstWindowNat i) (firstWindowNat j) : ℕ) : ℝ)^2/
          ((firstWindowNat i : ℝ)*(firstWindowNat j : ℝ)) ∧
    deficit N=(N : ℝ)-continuousCapacity N ∧ deficit 0=0 := by
  have h := gcdLcmSquareSum_eq_three_continuousCapacity N
  change (∑ i : FirstWindowIndex (N+1), ∑ j : FirstWindowIndex (N+1),
    ((Nat.gcd (firstWindowNat i) (firstWindowNat j) : ℕ) : ℝ)^2/
      ((firstWindowNat i : ℝ)*(firstWindowNat j : ℝ)))=3*continuousCapacity N at h
  refine ⟨by linarith,deficit_eq_capacity N,?_⟩
  simp [deficit]

theorem literal_reset_indicator_series :
    ∀ᵐ x ∂phaseHaar,
      Summable (fun k : ℕ => if x ∈ resetSet (k+2) then ((k+2 : ℕ) : ℝ)*collisionWeight (k+2) else 0) ∧
      increment x=(2/3 : ℝ)*(1-∑' k : ℕ,
        if x ∈ resetSet (k+2) then ((k+2 : ℕ) : ℝ)*collisionWeight (k+2) else 0) := by
  filter_upwards [resetTerm_from_two_hasSum_ae] with x hx
  have he : (fun k : ℕ => resetTerm (k+2) x)=
      (fun k : ℕ => if x ∈ resetSet (k+2) then ((k+2 : ℕ) : ℝ)*collisionWeight (k+2) else 0) := by
    funext k
    simp only [CollisionResetIntegrability.resetTerm,Set.indicator_apply]
  rw [he] at hx
  exact ⟨hx.summable,by rw [hx.tsum_eq]; rfl⟩

theorem collisionWeight_five : collisionWeight 5=(1/12 : ℝ) := by
  unfold collisionWeight reducedHarmonicStar
  rw [show Finset.Ico 1 5={1,2,3,4} by decide]
  norm_num [Finset.sum_filter,Nat.Coprime]

theorem collisionWeight_six : collisionWeight 6=(1/30 : ℝ) := by
  unfold collisionWeight reducedHarmonicStar
  rw [show Finset.Ico 1 6={1,2,3,4,5} by decide]
  norm_num [Finset.sum_filter,Nat.Coprime]

theorem reset_values_four_five_six :
    resetFunction (integerPhase 4)=5/6 ∧ resetFunction (integerPhase 5)=5/12 ∧
    resetFunction (integerPhase 6)=6/5 := by
  have h4 := resetFunction_integer (by norm_num : 0 < (4 : ℕ))
  have h5 := resetFunction_integer (by norm_num : 0 < (5 : ℕ))
  have h6 := resetFunction_integer (by norm_num : 0 < (6 : ℕ))
  norm_num at h4 h5 h6
  rw [h4,h5,h6]
  norm_num [show (4 : ℕ).divisors={1,2,4} by decide,
    show (5 : ℕ).divisors={1,5} by decide,show (6 : ℕ).divisors={1,2,3,6} by decide,
    collisionWeight_two,collisionWeight_three,collisionWeight_four,collisionWeight_five,collisionWeight_six]

theorem increment_values_four_five_six :
    increment (integerPhase 4)=1/9 ∧ increment (integerPhase 5)=7/18 ∧
    increment (integerPhase 6)=-(2/15 : ℝ) := by
  obtain ⟨h4,h5,h6⟩ := reset_values_four_five_six
  norm_num [increment,h4,h5,h6]

theorem deficit_values_four_five_six :
    deficit 4=13/9 ∧ deficit 5=11/6 ∧ deficit 6=17/10 := by
  simp only [deficit_eq_capacity,← completedCapacity_collision,completedCapacity]
  rw [show Finset.Icc 2 4={2,3,4} by decide,
    show Finset.Icc 2 5={2,3,4,5} by decide,
    show Finset.Icc 2 6={2,3,4,5,6} by decide]
  norm_num [collisionWeight_two,collisionWeight_three,collisionWeight_four,collisionWeight_five,collisionWeight_six]

theorem literal_reset_table :
    (resetFunction (integerPhase 4)=5/6 ∧ increment (integerPhase 4)=1/9 ∧ deficit 4=13/9) ∧
    (resetFunction (integerPhase 5)=5/12 ∧ increment (integerPhase 5)=7/18 ∧ deficit 5=11/6) ∧
    (resetFunction (integerPhase 6)=6/5 ∧ increment (integerPhase 6)=-(2/15 : ℝ) ∧ deficit 6=17/10) := by
  obtain ⟨f4,f5,f6⟩ := reset_values_four_five_six
  obtain ⟨g4,g5,g6⟩ := increment_values_four_five_six
  obtain ⟨d4,d5,d6⟩ := deficit_values_four_five_six
  exact ⟨⟨f4,g4,d4⟩,⟨f5,g5,d5⟩,⟨f6,g6,d6⟩⟩

theorem primitiveValue_six_table :
    (fun a : Fin 6 => primitiveValue 6 a)=![-1,-2,-1,1,2,1] := by
  funext a
  fin_cases a <;>
    norm_num [primitiveValue_formula,show (6 : ℕ).divisors={1,2,3,6} by decide,
      centeredRemainder,ArithmeticFunction.moebius,Nat.prime_two.squarefree,Nat.prime_three.squarefree]

theorem amplitude_log_two_bound {q : ℕ} (hq : 2 ≤ q) :
    amplitude q ≤ (2*amplitudeLogConstant)*Real.log (2*(q : ℝ))/(q : ℝ)^2 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog := Real.log_natCast_nonneg q
  have htwo := Real.log_two_gt_d9
  have hnum : 1+Real.log q ≤ 2*Real.log (2*(q : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne']
    linarith
  have h := mul_le_mul_of_nonneg_left hnum amplitudeLogConstant_pos.le
  have hb := amplitude_log_bound hq
  unfold positiveLogKernel at hb
  rw [← mul_div_assoc] at hb
  exact hb.trans (by
    have := div_le_div_of_nonneg_right h (sq_nonneg (q : ℝ))
    convert! this using 1
    ring)

theorem amplitude_isBigO_log_two_div_square :
    IsBigO atTop amplitude (fun q : ℕ => Real.log (2*(q : ℝ))/(q : ℝ)^2) := by
  apply isBigO_iff.mpr
  refine ⟨2*amplitudeLogConstant,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with q hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (2*(q : ℝ)) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (amplitude_nonneg q),Real.norm_of_nonneg (div_nonneg hl (sq_nonneg _))]
  simpa only [mul_div_assoc] using amplitude_log_two_bound hq

end NField.Alignment.CollisionElementaryDisplays
