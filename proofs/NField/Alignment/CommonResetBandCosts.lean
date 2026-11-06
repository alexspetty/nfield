/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandWeighted
import NField.Alignment.CommonResetRootSums

/-! # The literal three band costs in separated frequency variables -/

noncomputable section

namespace NField.Alignment.CommonResetBandCosts

open scoped BigOperators
open CommonResetBandWeighted CommonResetBandScale CommonResetRootSums CommonResetSmallConductors

/-- Title: `The three completed band terms equal the printed separate frequency costs`. -/
theorem band_cost_decomposition {p m u v j : ℕ}
    (hm : 0 < m) (hu : 0 < u) (hv : 0 < v) (hj : 0 < j) :
    Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j =
      ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
        (Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ))*(1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ)) +
      ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*
        (Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ))*rootCube j*rootCube v +
      ((p : ℝ)/m)*(Real.sqrt ((j*v).gcd u : ℝ)/Real.sqrt (u : ℝ))*
        (1/(j : ℝ))*(1/(v : ℝ))*Real.log (2*(u : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hsu0 := (Real.sqrt_pos.mpr huR).ne'
  have hsv0 := (Real.sqrt_pos.mpr hvR).ne'
  have hsj0 := (Real.sqrt_pos.mpr hjR).ne'
  have hsm0 := (Real.sqrt_pos.mpr hmR).ne'
  have hsu := Real.sq_sqrt huR.le
  have hsv := Real.sq_sqrt hvR.le
  have hsj := Real.sq_sqrt hjR.le
  unfold bandSummandScale bandPhaseScale rootCube
  rw [Real.sqrt_mul hjR.le]
  field_simp
  ring_nf
  simp only [hsu, hsv, hsj]
  ring

theorem harmonic_one_le {p : ℕ} (hp : 1 ≤ p) : (1 : ℝ) ≤ harmonic p := by
  have h := harmonic_monotone hp
  simpa using h

theorem log_twice_le_harmonic {p u : ℕ} (hu : 0 < u) (hup : u ≤ p) :
    Real.log (2*(u : ℝ)) ≤ 2*(harmonic p : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlogu : Real.log (u : ℝ) ≤ harmonic u := by
    have h := log_add_one_le_harmonic u
    exact (Real.log_le_log huR (by push_cast; linarith : (u : ℝ) ≤ (u+1 : ℕ))).trans h
  have hh := harmonic_monotone hup
  have hH := harmonic_one_le (show 1 ≤ p by omega)
  rw [Real.log_mul (by norm_num) huR.ne']
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

end NField.Alignment.CommonResetBandCosts
