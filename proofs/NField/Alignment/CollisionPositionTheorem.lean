/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorOne
import NField.Alignment.CollisionIntegerSingularity

/-!
# Position stability and its divisibility limit

Both address-one gaps tend to two thirds while their endpoint scales diverge.
The full proposition is assembled without maximal-order or extrema hypotheses.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositionTheorem

open scoped BigOperators Classical
open Filter
open CollisionRemainderDynamics CollisionPotentialConvergence CollisionCylinderMeans
open CollisionJordanVariance CollisionOdometerRecurrence CollisionIntegerSingularity
open CollisionPositionStability CollisionCylinderOne CollisionConductorOne CollisionLogTailKernel

theorem stationaryAge_le_alignment (M : ℕ) :
    stationaryAge collisionWeight M ≤ alignmentConstant (cutoffPeriod M) := by
  have hn : ∀ k, 0 ≤ collisionWeight k*((k.gcd (cutoffPeriod M) : ℝ)-1) := by
    intro k
    apply mul_nonneg (collisionWeight_nonneg k)
    have h : (1 : ℝ) ≤ k.gcd (cutoffPeriod M) := by
      exact_mod_cast Nat.gcd_pos_of_pos_right k (cutoffPeriod_pos M)
    linarith
  have h := (alignment_series_summable (cutoffPeriod_pos M)).sum_le_tsum (Finset.Icc 2 M)
    (fun k _ => hn k)
  have he : (∑ k ∈ Finset.Icc 2 M, collisionWeight k*((k.gcd (cutoffPeriod M) : ℝ)-1))=
      ∑ k ∈ Finset.Icc 2 M, collisionWeight k*((k : ℝ)-1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.gcd_eq_left_iff_dvd.mpr
      (dvd_cutoffPeriod (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2)]
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/3)

theorem totient_cutoff_sum {k M : ℕ} (hk : 0 < k) (hM : k ≤ M) :
    (∑ q ∈ Finset.Icc 2 M, if q ∣ k then (q.totient : ℝ) else 0)=(k : ℝ)-1 := by
  have he : (Finset.Icc 2 M).filter (fun q => q ∣ k)=k.divisors.filter (fun q => 2 ≤ q) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨⟨h.2,hk.ne'⟩,h.1.1⟩
    · intro h
      exact ⟨⟨h.2,(Nat.le_of_dvd hk h.1.1).trans hM⟩,h.1.1⟩
  rw [← Finset.sum_filter,he,Finset.sum_filter,totient_divisor_sum_ge_two hk]

theorem finiteTotientAmplitude_sum (M : ℕ) :
    (∑ q ∈ Finset.Icc 2 M, (q.totient : ℝ)*finiteAmplitude collisionWeight q M)=
      ∑ k ∈ Finset.Icc 2 M, collisionWeight k*((k : ℝ)-1) := by
  calc
    _ = ∑ q ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M,
        collisionWeight k*(if q ∣ k then (q.totient : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [finiteAmplitude,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    _ = ∑ k ∈ Finset.Icc 2 M, collisionWeight k*
        (∑ q ∈ Finset.Icc 2 M, if q ∣ k then (q.totient : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [totient_cutoff_sum (by have := (Finset.mem_Icc.mp hk).1; omega)
        (Finset.mem_Icc.mp hk).2]

theorem stationaryAge_le_conductorEndpoint (M : ℕ) :
    stationaryAge collisionWeight M ≤ conductorEndpoint M := by
  have h := Finset.sum_le_sum (s := Finset.Icc 2 M) (fun q _ =>
    mul_le_mul_of_nonneg_left (finiteAmplitude_le_amplitude q M) (Nat.cast_nonneg q.totient))
  rw [finiteTotientAmplitude_sum] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/3)

theorem alignment_cutoff_tendsto_atTop :
    Tendsto (fun M => alignmentConstant (cutoffPeriod M)) atTop atTop :=
  tendsto_atTop_mono stationaryAge_le_alignment stationaryAge_tendsto_atTop

theorem conductorEndpoint_tendsto_atTop : Tendsto conductorEndpoint atTop atTop :=
  tendsto_atTop_mono stationaryAge_le_conductorEndpoint stationaryAge_tendsto_atTop

theorem log_double_over_nat_tendsto_zero :
    Tendsto (fun M : ℕ => Real.log (2*(M : ℝ))/(M : ℝ)) atTop (nhds 0) := by
  have h1 := (logPower_div_linear_tendsto 1).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [pow_one,Function.comp_def] at h1
  have h2 : Tendsto (fun M : ℕ => Real.log 2/(M : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := h2.add h1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hM0 : (M : ℝ)≠0 := by exact_mod_cast (by omega : M≠0)
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hM0]
  ring

theorem cylinder_one_gap_tendsto :
    Tendsto (fun M => cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M))
      atTop (nhds (2/3 : ℝ)) := by
  have h := (cylinder_address_one_asymptotic.trans_tendsto log_double_over_nat_tendsto_zero).add_const
    (2/3 : ℝ)
  simpa only [sub_add_cancel,zero_add] using h

theorem conductor_one_gap_tendsto :
    Tendsto (fun Q => fixedConductorValue Q 1+conductorEndpoint Q) atTop (nhds (2/3 : ℝ)) := by
  have h := (conductor_address_one_asymptotic.trans_tendsto log_double_over_nat_tendsto_zero).add_const
    (2/3 : ℝ)
  simpa only [sub_add_cancel,zero_add] using h

theorem cylinder_one_relative_gap_tendsto :
    Tendsto (fun M => (cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M))/
      (2*alignmentConstant (cutoffPeriod M))) atTop (nhds 0) := by
  have h := (cylinder_one_gap_tendsto.div_atTop alignment_cutoff_tendsto_atTop).const_mul (1/2 : ℝ)
  simp only [mul_zero] at h
  convert! h using 1
  funext M
  ring

theorem conductor_one_relative_gap_tendsto :
    Tendsto (fun Q => (fixedConductorValue Q 1+conductorEndpoint Q)/(2*conductorEndpoint Q))
      atTop (nhds 0) := by
  have h := (conductor_one_gap_tendsto.div_atTop conductorEndpoint_tendsto_atTop).const_mul (1/2 : ℝ)
  simp only [mul_zero] at h
  convert! h using 1
  funext Q
  ring

theorem address_one_not_divisible {p : ℕ} (hp : 2 ≤ p) : ¬p ∣ 1 := by
  intro hd
  have h := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 1) hd
  omega

theorem position_stability_and_divisibility_limit :
    (∀ L : ℕ, 2 ≤ L →
      (∀ k, 0 ≤ positionWeight L k) ∧ Summable (positionWeight L) ∧
      (∑' k, positionWeight L k)=1 ∧
      (∀ a, (cylinderMean L a+alignmentConstant L)/(2*alignmentConstant L)=
        ∑' k, positionWeight L k*relativePosition L a k) ∧
      (∀ (a : ℕ) (ε δ : ℝ), 0 < δ →
        cylinderMean L a+alignmentConstant L ≤ ε*alignmentConstant L →
        positionExceedanceMass L a δ ≤ ε/(2*δ))) ∧
    Asymptotics.IsBigO atTop
      (fun M : ℕ => cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M)-(2/3 : ℝ))
      (fun M : ℕ => Real.log (2*(M : ℝ))/(M : ℝ)) ∧
    Asymptotics.IsBigO atTop
      (fun Q : ℕ => fixedConductorValue Q 1+conductorEndpoint Q-(2/3 : ℝ))
      (fun Q : ℕ => Real.log (2*(Q : ℝ))/(Q : ℝ)) ∧
    Tendsto (fun M => (cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M))/
      (2*alignmentConstant (cutoffPeriod M))) atTop (nhds 0) ∧
    Tendsto (fun Q => (fixedConductorValue Q 1+conductorEndpoint Q)/(2*conductorEndpoint Q))
      atTop (nhds 0) ∧
    (∀ p : ℕ, 2 ≤ p → ¬p ∣ 1) := by
  refine ⟨?_,cylinder_address_one_asymptotic,conductor_address_one_asymptotic,
    cylinder_one_relative_gap_tendsto,conductor_one_relative_gap_tendsto,
    fun _ hp => address_one_not_divisible hp⟩
  intro L hL
  exact ⟨positionWeight_nonneg hL,positionWeight_summable hL,positionWeight_tsum hL,
    normalized_cylinder_position hL,fun a ε δ hδ hg => position_stability hL a hδ hg⟩

end NField.Alignment.CollisionPositionTheorem
