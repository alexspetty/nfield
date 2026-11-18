/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreRegular
import NField.Alignment.RealBernoulliBoundaryLimits
/-! # One-sided limits of the weighted field and its fibre path

Contact masses are evaluated on the complete source before taking either
one-sided limit. Assigned midpoint values remain separate from both traces.
-/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators Topology
open Filter Set NField.Alignment CommonResetGram CollisionRampEnergy
open CollisionDedekindPairing RealSawtoothLimits RealBernoulliBoundaryLimits FibreReconstruction

def contactMass (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, if Int.fract ((j : ℝ)*x)=0 then c j else 0

def profileLeft (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  weightedProfile N c x+contactMass N c x

def profileRight (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  weightedProfile N c x-contactMass N c x

theorem weighted_profile_left_limit (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    Tendsto (weightedProfile N c) (𝓝[<] x) (𝓝 (profileLeft N c x)) := by
  have h := tendsto_finsetSum (Finset.Icc 1 N) fun j hj =>
    ((sawtooth_left ((j : ℝ)*x)).comp
      (positive_mul_left_limit (by exact_mod_cast (Finset.mem_Icc.mp hj).1) x)).const_mul (c j)
  have ht := h.const_mul 2
  convert ht using 1
  · rfl
  · congr 1
    unfold profileLeft weightedProfile contactMass
    simp only [midpoint_row_periodic_saw, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring

theorem weighted_profile_right_limit (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    Tendsto (weightedProfile N c) (𝓝[>] x) (𝓝 (profileRight N c x)) := by
  have h := tendsto_finsetSum (Finset.Icc 1 N) fun j hj =>
    ((sawtooth_right ((j : ℝ)*x)).comp
      (positive_mul_right_limit (by exact_mod_cast (Finset.mem_Icc.mp hj).1) x)).const_mul (c j)
  have ht := h.const_mul 2
  convert ht using 1
  · rfl
  · congr 1
    unfold profileRight weightedProfile contactMass
    simp only [midpoint_row_periodic_saw, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring

def fibreLeft (p : ℕ) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) : ℝ :=
  profileLeft (p-1) c (((v.val : ℝ)+u)/(p : ℝ))-profileLeft (p-1) c u/(p : ℝ)

def fibreRight (p : ℕ) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) : ℝ :=
  profileRight (p-1) c (((v.val : ℝ)+u)/(p : ℝ))-profileRight (p-1) c u/(p : ℝ)

theorem affine_fibre_left_limit {p : ℕ} (hp : 0 < p) (v : ℕ) (u : ℝ) :
    Tendsto (fun x : ℝ => ((v : ℝ)+x)/(p : ℝ)) (𝓝[<] u)
      (𝓝[<] (((v : ℝ)+u)/(p : ℝ))) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuousAt_const.add continuousAt_id).div_const (p : ℝ)).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x < u at hx
    change ((v : ℝ)+x)/(p : ℝ) < ((v : ℝ)+u)/(p : ℝ)
    exact div_lt_div_of_pos_right (by linarith) (by exact_mod_cast hp)

theorem affine_fibre_right_limit {p : ℕ} (hp : 0 < p) (v : ℕ) (u : ℝ) :
    Tendsto (fun x : ℝ => ((v : ℝ)+x)/(p : ℝ)) (𝓝[>] u)
      (𝓝[>] (((v : ℝ)+u)/(p : ℝ))) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuousAt_const.add continuousAt_id).div_const (p : ℝ)).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change u < x at hx
    change ((v : ℝ)+u)/(p : ℝ) < ((v : ℝ)+x)/(p : ℝ)
    exact div_lt_div_of_pos_right (by linarith) (by exact_mod_cast hp)

theorem fibre_path_left_limit {p : ℕ} (hp : 0 < p) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) :
    Tendsto (fun x => fibrePath p c x v) (𝓝[<] u) (𝓝 (fibreLeft p c u v)) := by
  exact ((weighted_profile_left_limit (p-1) c _).comp (affine_fibre_left_limit hp v.val u)).sub
    ((weighted_profile_left_limit (p-1) c u).div_const (p : ℝ))

theorem fibre_path_right_limit {p : ℕ} (hp : 0 < p) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) :
    Tendsto (fun x => fibrePath p c x v) (𝓝[>] u) (𝓝 (fibreRight p c u v)) := by
  exact ((weighted_profile_right_limit (p-1) c _).comp (affine_fibre_right_limit hp v.val u)).sub
    ((weighted_profile_right_limit (p-1) c u).div_const (p : ℝ))

theorem fibre_jump_contact_formula (p : ℕ) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) :
    fibreRight p c u v-fibreLeft p c u v=
      -2*(contactMass (p-1) c (((v.val : ℝ)+u)/(p : ℝ))-contactMass (p-1) c u/(p : ℝ)) := by
  unfold fibreRight fibreLeft profileRight profileLeft
  ring

end NField.ResetForests.FibreTraces
