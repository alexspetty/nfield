/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevEndpointIndices
import NField.Alignment.KorolevWindowMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Korolev's selected scales in logarithmic coordinates

Write v=log(log m), u=log(log x), c=log C. The source lower range
becomes (4/5)*v+5*log v < u; we prove estimates also at equality.
The source upper range implies u<=v. All thresholds below are independent
of u, so they retain uniformity across that range.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceScales
open Filter
open scoped Topology

def gain (v u c : ℝ) : ℝ := (5*u-4*v-Real.log v-c)/24
def pStart (v u c : ℝ) : ℝ := Real.exp (v-u+2*gain v u c)/2
def pStop (v u c : ℝ) : ℝ := Real.exp (v-u+4*gain v u c)/2
def qStart (v u c : ℝ) : ℝ := 2*Real.exp (2*v-2*u+8*gain v u c)
def qStop (v u c : ℝ) : ℝ := 2*Real.exp (2*v-2*u+10*gain v u c)
def pThreshold (v u c : ℝ) : ℝ := Real.exp (u-2*gain v u c)
def qThreshold (v u c : ℝ) : ℝ := Real.exp (2*u-v-8*gain v u c)/4

theorem pStop_ratio (v u c : ℝ) : pStop v u c = pStart v u c * Real.exp (2*gain v u c) := by
  unfold pStop pStart
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

theorem qStop_ratio (v u c : ℝ) : qStop v u c = qStart v u c * Real.exp (2*gain v u c) := by
  unfold qStop qStart
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem pStart_threshold (v u c : ℝ) : Real.exp v/(2*pThreshold v u c) = pStart v u c := by
  unfold pThreshold pStart
  rw [mul_comm 2, div_mul_eq_div_div, ← Real.exp_sub]
  congr 2
  ring

theorem qStart_threshold (v u c : ℝ) : Real.exp v/(2*qThreshold v u c) = qStart v u c := by
  unfold qThreshold qStart
  have he : 2*v-2*u+8*gain v u c = v-(2*u-v-8*gain v u c) := by ring
  rw [he, Real.exp_sub v (2*u-v-8*gain v u c)]
  field_simp
  norm_num

theorem eventual_scale_bounds (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      0 < u ∧ 0 ≤ gain v u c ∧ 2 ≤ pStart v u c ∧ 2 ≤ qStart v u c ∧
      4 ≤ Real.exp (2*gain v u c) ∧ 2*u ≤ Real.exp (2*gain v u c) ∧
      pStop v u c ≤ 2*Real.exp (5*v/12) ∧ qStop v u c ≤ 2*Real.exp (5*v/12) := by
  have hl := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hl, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (2*(c+12*Real.log 4)),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 2+c/12)]
    with v hv hv2 hvC hvlog u hulo hule
  have hv0 : 0 < v := by linarith
  have hw : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  change |Real.log v| ≤ (1/2)*|v| at hv
  rw [abs_of_nonneg hw, abs_of_nonneg hv0.le] at hv
  have hu0 : 0 < u := by linarith
  have hg : Real.log v-c/24 ≤ gain v u c := by unfold gain; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg0 : 0 ≤ gain v u c := by linarith
  have hex : 2*v ≤ Real.exp (2*gain v u c) := by
    have hh : Real.log 2+Real.log v ≤ 2*gain v u c := by linarith
    have hh' := Real.exp_le_exp.mpr hh
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hv0] at hh'
    exact hh'
  have hpa : 2 ≤ pStart v u c := by
    have hh : Real.log 4 ≤ v-u+2*gain v u c := by unfold gain; linarith
    have hh' := Real.exp_le_exp.mpr hh
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hh'
    unfold pStart
    linarith
  have hqa : 2 ≤ qStart v u c := by
    have hh : 0 ≤ 2*v-2*u+8*gain v u c := by linarith
    have hh' := Real.exp_le_exp.mpr hh
    rw [Real.exp_zero] at hh'
    unfold qStart
    linarith
  refine ⟨hu0, hg0, hpa, hqa, by linarith, by linarith, ?_, ?_⟩
  · have hh : v-u+4*gain v u c ≤ 5*v/12 := by unfold gain; linarith
    have hh' := Real.exp_le_exp.mpr hh
    unfold pStop
    linarith [Real.exp_pos (5*v/12)]
  · have hh : 2*v-2*u+10*gain v u c ≤ 5*v/12 := by unfold gain; linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (by norm_num)

theorem threshold_cutoff_bounds {v u c : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hg : 0 ≤ gain v u c) (hm : u ≤ Real.exp (2*gain v u c)) :
    pThreshold v u c ≤ Real.exp u/u ∧ qThreshold v u c ≤ Real.exp u/u := by
  have hp : pThreshold v u c ≤ Real.exp u/u := by
    unfold pThreshold
    rw [Real.exp_sub]
    exact div_le_div_of_nonneg_left (Real.exp_pos u).le hu hm
  refine ⟨hp, le_trans ?_ hp⟩
  have hh : 2*u-v-8*gain v u c ≤ u-2*gain v u c := by linarith
  have hh' := Real.exp_le_exp.mpr hh
  unfold qThreshold pThreshold
  linarith [Real.exp_pos (2*u-v-8*gain v u c)]

end NField.Alignment.KorolevSourceScales
