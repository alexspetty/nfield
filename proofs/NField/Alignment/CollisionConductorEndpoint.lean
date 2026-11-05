/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionInverseRemainder
import NField.Alignment.CollisionStationaryAgeAsymptotic

/-!
# The full-amplitude conductor endpoint asymptotic

The uniform inverse remainder is summed over the finite endpoint weights.
The comparison is with the actual truncated stationary age, whose leading
coefficient and logarithmic error were proved separately.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorEndpoint

open scoped BigOperators Classical
open Filter
open CollisionRemainderDynamics CollisionConductorOne CollisionFiniteRegrouping
open CollisionInverseRemainder CollisionAmplitudeTail CollisionStationaryAgeAsymptotic

def endpointError (Q : ℕ) : ℝ := conductorEndpoint Q-stationaryAge collisionWeight Q

theorem endpointError_formula (Q : ℕ) :
    endpointError Q=(1/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q,
      (beta d Q-collisionWeight d)*((d : ℝ)-1) := by
  rw [endpointError,conductorEndpoint_beta,stationaryAge,← mul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem endpointError_term_bound {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    |(beta d Q-collisionWeight d)*((d : ℝ)-1)| ≤
      (16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/(Q : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd0 : (0 : ℝ) < d := by linarith
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hl : 0 ≤ Real.log (2*(Q : ℝ)) := Real.log_nonneg (by
    have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (show 2 ≤ Q by omega)
    linarith)
  rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hdR)]
  calc
    _ ≤ ((16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/((d : ℝ)*(Q : ℝ)))*((d : ℝ)-1) :=
      mul_le_mul_of_nonneg_right (beta_inverse_uniform_bound hd hdQ) (sub_nonneg.mpr hdR)
    _ ≤ ((16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/((d : ℝ)*(Q : ℝ)))*(d : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity [amplitudeLogConstant_pos])
    _ = _ := by field_simp

theorem endpointError_bound {Q : ℕ} (hQ : 2 ≤ Q) :
    |endpointError Q| ≤ (16*amplitudeLogConstant/3)*Real.log (2*(Q : ℝ)) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hl : 0 ≤ Real.log (2*(Q : ℝ)) := Real.log_nonneg (by
    have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith)
  have hc : ((Finset.Icc 2 Q).card : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast (show (Finset.Icc 2 Q).card ≤ Q by rw [Nat.card_Icc]; omega)
  rw [endpointError_formula,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/3)]
  calc
    _ ≤ (1/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, |(beta d Q-collisionWeight d)*((d : ℝ)-1)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/3 : ℝ)*∑ _d ∈ Finset.Icc 2 Q,
        (16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/(Q : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro d hd
      exact endpointError_term_bound (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    _ ≤ (1/3 : ℝ)*(Q : ℝ)*((16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/(Q : ℝ)) := by
      rw [Finset.sum_const,nsmul_eq_mul,← mul_assoc]
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity [amplitudeLogConstant_pos])
    _ = _ := by field_simp

theorem endpointError_isBigO_log :
    Asymptotics.IsBigO atTop endpointError (fun Q : ℕ => Real.log (2*(Q : ℝ))) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16*amplitudeLogConstant/3,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hl : 0 ≤ Real.log (2*(Q : ℝ)) := Real.log_nonneg (by
    have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith)
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hl]
  exact endpointError_bound hQ

theorem conductorEndpoint_isBigO_log :
    Asymptotics.IsBigO atTop
      (fun Q : ℕ => conductorEndpoint Q-Real.log (Q : ℝ)^2/Real.pi^2)
      (fun Q : ℕ => Real.log (2*(Q : ℝ))) := by
  have h := endpointError_isBigO_log.add stationaryAge_isBigO_log
  convert! h using 1
  funext Q
  unfold endpointError
  ring

end NField.Alignment.CollisionConductorEndpoint
