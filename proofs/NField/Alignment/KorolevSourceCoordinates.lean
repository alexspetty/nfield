/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevWindowParameters

/-!
# Exact power-form correspondence for the source scales

With epsilon=exp(u)/exp(v), Y=exp(u), and gamma=gain/u, these are
exactly the source's four index scales. No asymptotic equivalence is used.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceCoordinates
open KorolevSourceScales KorolevEndpointIndices KorolevWindowParameters KorolevPrimeWindows
  Filter
open scoped Topology

theorem gain_power (r u g : ℝ) (hu : u ≠ 0) :
    (Real.exp u)^(r*(g/u)) = Real.exp (r*g) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

theorem single_scale (r v u g : ℝ) (hu : u ≠ 0) :
    Real.exp (v-u+r*g)/2 =
      (1/(2*(Real.exp u/Real.exp v)))*(Real.exp u)^(r*(g/u)) := by
  rw [gain_power r u g hu, Real.exp_add, Real.exp_sub]
  field_simp

theorem double_scale (r v u g : ℝ) (hu : u ≠ 0) :
    2*Real.exp (2*v-2*u+r*g) =
      (2/(Real.exp u/Real.exp v)^2)*(Real.exp u)^(r*(g/u)) := by
  rw [gain_power r u g hu, Real.exp_add,
    show 2*v-2*u = (2 : ℕ)*(v-u) by push_cast; ring,
    Real.exp_nat_mul, Real.exp_sub]
  field_simp

theorem scale_correspondence (v u c : ℝ) (hu : u ≠ 0) :
    pStart v u c = (1/(2*(Real.exp u/Real.exp v)))*(Real.exp u)^(2*(gain v u c/u)) ∧
    pStop v u c = (1/(2*(Real.exp u/Real.exp v)))*(Real.exp u)^(4*(gain v u c/u)) ∧
    qStart v u c = (2/(Real.exp u/Real.exp v)^2)*(Real.exp u)^(8*(gain v u c/u)) ∧
    qStop v u c = (2/(Real.exp u/Real.exp v)^2)*(Real.exp u)^(10*(gain v u c/u)) :=
  ⟨single_scale 2 v u _ hu, single_scale 4 v u _ hu,
    double_scale 8 v u _ hu, double_scale 10 v u _ hu⟩

theorem threshold_power (r u g : ℝ) (hu : u ≠ 0) :
    Real.exp (u-r*g) = (Real.exp u)^(1-r*(g/u)) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

theorem double_threshold_power (r v u g : ℝ) (hu : u ≠ 0) :
    Real.exp (2*u-v-r*g)/4 =
      (Real.exp u/Real.exp v)*(Real.exp u)^(1-r*(g/u))/4 := by
  rw [← threshold_power r u g hu, ← Real.exp_sub, ← Real.exp_add]
  congr 2
  ring


theorem eventual_endpoint_definitions (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      (upperEndpoint (Real.exp v) (pFirst v u c) ≤ Real.exp (pThreshold v u c)/4 ∧
        Real.exp (pThreshold v u c)/4 < upperEndpoint (Real.exp v) (pFirst v u c-1)) ∧
      (Real.exp (Real.exp (u-4*gain v u c))/4 ≤ upperEndpoint (Real.exp v) (pLast v u c+1) ∧
        upperEndpoint (Real.exp v) (pLast v u c+1+1) < Real.exp (Real.exp (u-4*gain v u c))/4) ∧
      (upperEndpoint (Real.exp v) (qFirst v u c) ≤ Real.exp (qThreshold v u c)/4 ∧
        Real.exp (qThreshold v u c)/4 < upperEndpoint (Real.exp v) (qFirst v u c-1)) ∧
      (Real.exp (Real.exp (2*u-v-10*gain v u c)/4)/4 ≤ upperEndpoint (Real.exp v) (qLast v u c) ∧
        upperEndpoint (Real.exp v) (qLast v u c+1) < Real.exp (Real.exp (2*u-v-10*gain v u c)/4)/4) := by
  filter_upwards [eventual_scale_bounds c hc] with v hv u hulo hule
  obtain ⟨_, _, hpA, hqA, hR, _, _, _⟩ := hv u hulo hule
  have hpB : 2 ≤ pStop v u c := by
    rw [pStop_ratio]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ pStart v u c by linarith)]
  have hqB : 2 ≤ qStop v u c := by
    rw [qStop_ratio]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ qStart v u c by linarith)]
  have hpstop : Real.exp v/(2*Real.exp (u-4*gain v u c)) = pStop v u c := by
    unfold pStop
    rw [mul_comm 2, div_mul_eq_div_div, ← Real.exp_sub]
    congr 2
    ring
  have hqstop : Real.exp v/(2*(Real.exp (2*u-v-10*gain v u c)/4)) = qStop v u c := by
    unfold qStop
    rw [show 2*v-2*u+10*gain v u c = v-(2*u-v-10*gain v u c) by ring,
      Real.exp_sub v (2*u-v-10*gain v u c)]
    field_simp
    norm_num
  have hp1 := lowerIndex_endpoint (Real.exp_pos _) hpA (pStart_threshold v u c)
  have hp2 := upperIndex_endpoint (Real.exp_pos _) hpB hpstop (by norm_num : (1 : ℕ) ≤ 1)
  have hq1 := lowerIndex_endpoint (by unfold qThreshold; positivity) hqA (qStart_threshold v u c)
  have hq2 := upperIndex_endpoint (by positivity : 0 < Real.exp (2*u-v-10*gain v u c)/4)
    hqB hqstop (by norm_num : (0 : ℕ) ≤ 1)
  simpa only [pFirst, pLast, qFirst, qLast, Nat.add_zero] using ⟨hp1, hp2, hq1, hq2⟩

end NField.Alignment.KorolevSourceCoordinates
