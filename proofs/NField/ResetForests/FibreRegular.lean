/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreDirections
import NField.Alignment.RealSawtoothLimits
import Mathlib.Analysis.Calculus.MeanValue
/-! # Constancy of the actual fibre path away from resets -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators Topology
open Set NField.Alignment CommonResetGram CollisionRampEnergy
open CollisionDedekindPairing RealSawtoothLimits SourceMetrics FibreReconstruction

def regularAt (N : ℕ) (u : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 N, Int.fract ((j : ℝ)*u) ≠ 0

theorem regular_at_fibre {N p : ℕ} (hp : 0 < p) (u : ℝ) (v : ℕ)
    (hu : regularAt N u) : regularAt N (((v : ℝ)+u)/(p : ℝ)) := by
  intro j hj hz
  apply hu j hj
  obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hz
  apply Int.fract_eq_zero_iff.mpr
  refine ⟨(p : ℤ)*n-(j : ℤ)*(v : ℤ), ?_⟩
  have he : (p : ℝ)*(n : ℝ)=(j : ℝ)*((v : ℝ)+u) := by
    rw [hn]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
  push_cast
  nlinarith

theorem weighted_profile_derivative {N : ℕ} (c : ℕ → ℝ) (u : ℝ)
    (hu : regularAt N u) :
    HasDerivAt (weightedProfile N c) (2*sourceSlope N c) u := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      HasDerivAt (fun x => c j*midpointRow j x) (c j*(j : ℝ)) u := by
    have h := (sawtooth_deriv (hu j hj)).comp u
      ((hasDerivAt_id u).const_mul (j : ℝ))
    convert! h.const_mul (c j) using 1
    ring
  convert! (HasDerivAt.fun_sum hterm).const_mul 2 using 1

theorem fibre_path_derivative_zero {p : ℕ} (hp : 0 < p) (c : ℕ → ℝ)
    (u : ℝ) (hu : regularAt (p-1) u) (v : Fin p) :
    HasDerivAt (fun x => fibrePath p c x v) 0 u := by
  have hinner : HasDerivAt (fun x : ℝ => ((v.val : ℝ)+x)/(p : ℝ))
      (1/(p : ℝ)) u := by
    convert! ((hasDerivAt_id u).add_const (v.val : ℝ)).div_const (p : ℝ) using 1
    simp only [id_eq, add_comm]
  have hs := (weighted_profile_derivative c _ (regular_at_fibre hp u v.val hu)).comp u hinner
  have hm := (weighted_profile_derivative c u hu).div_const (p : ℝ)
  convert! hs.sub hm using 1
  ring

theorem fibre_path_constant_on_interval {p : ℕ} (hp : 0 < p) (c : ℕ → ℝ)
    (a b : ℝ) (hregular : ∀ u ∈ Ioo a b, regularAt (p-1) u)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    fibrePath p c x=fibrePath p c y := by
  funext v
  have hbound := (convex_Ioo a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun u hu => (fibre_path_derivative_zero hp c u (hregular u hu) v).hasDerivWithinAt)
    (by simp) hx hy
  have hz : fibrePath p c y v-fibrePath p c x v=0 := by
    apply norm_eq_zero.mp
    have hbound0 : ‖fibrePath p c y v-fibrePath p c x v‖ ≤ 0 := by simpa using hbound
    exact hbound0.antisymm (norm_nonneg _)
  exact (sub_eq_zero.mp hz).symm

end NField.ResetForests.FibreTraces
