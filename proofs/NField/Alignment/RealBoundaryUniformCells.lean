/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBernoulliJumpData
import NField.Alignment.RealSawtoothDistribution
import Mathlib.Data.Nat.Factorial.Basic

/-! # A common finite partition for every actual Bernoulli boundary jump -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealBoundaryUniformCells
open scoped BigOperators Topology
open Filter Set CollisionDedekindPairing RealSawtoothLimits RealBernoulliBoundaryLimits
  RealBernoulliJumpData

def grid (D j : ℕ) : ℝ := (j : ℝ)/(D : ℝ)

theorem grid_step {D : ℕ} (hD : 0<D) (j : ℕ) : grid D j<grid D (j+1) := by
  unfold grid
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hD)
  exact_mod_cast Nat.lt_succ_self j

theorem grid_floor_bounds {D r j : ℕ} {x : ℝ} (hD : 0<D) (hr : 0<r)
    (hrD : r∣D) (hx : x∈Ioo (grid D j) (grid D (j+1))) :
    ((j/(D/r) : ℕ) : ℝ)<(r : ℝ)*x ∧
      (r : ℝ)*x<((j/(D/r) : ℕ) : ℝ)+1 := by
  let q := D/r
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd hD hrD) hr
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hDR : (0 : ℝ)<D := by exact_mod_cast hD
  have hmul : (r : ℝ)*(q : ℝ)=D := by exact_mod_cast Nat.mul_div_cancel' hrD
  have hlo := (div_lt_iff₀ hDR).mp hx.1
  have hhi := (lt_div_iff₀ hDR).mp hx.2
  have hdivlo : (q : ℝ)*((j/q : ℕ) : ℝ)≤j := by exact_mod_cast Nat.mul_div_le j q
  have hdivhi : (j : ℝ)+1≤(q : ℝ)*(((j/q : ℕ) : ℝ)+1) := by
    have hm := Nat.mod_lt j hq
    have he := Nat.mod_add_div j q
    have hh : j+1≤q*(j/q+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    exact_mod_cast hh
  change ((j/q : ℕ) : ℝ)<(r : ℝ)*x ∧ (r : ℝ)*x<((j/q : ℕ) : ℝ)+1
  have hcast : ((j+1 : ℕ) : ℝ)=(j : ℝ)+1 := by push_cast; rfl
  change (j : ℝ)<x*(D : ℝ) at hlo
  change x*(D : ℝ)<((j+1 : ℕ) : ℝ) at hhi
  rw [hcast] at hhi
  rw [← hmul] at hlo hhi
  constructor <;> nlinarith

def cellIntercept (N j : ℕ) : ℝ :=
  -(N : ℝ)-2*∑ r ∈ Finset.range N,((j/(N.factorial/(r+1)) : ℕ) : ℝ)

def cellBoundary (N j : ℕ) (x : ℝ) : ℝ := realSlope N*x+cellIntercept N j

theorem boundary_on_cell (N j : ℕ) {x : ℝ}
    (hx : x∈Ioo (grid N.factorial j) (grid N.factorial (j+1))) :
    realBoundary N x=cellBoundary N j x := by
  have hterm (r : ℕ) (hr : r∈Finset.range N) :
      periodicSawtooth (((r+1 : ℕ) : ℝ)*x)=
        ((r+1 : ℕ) : ℝ)*x-((j/(N.factorial/(r+1)) : ℕ) : ℝ)-1/2 := by
    have hrN := Finset.mem_range.mp hr
    have hb := grid_floor_bounds (Nat.factorial_pos N) (Nat.succ_pos r)
      (Nat.dvd_factorial (Nat.succ_pos r) (by omega : r+1≤N)) hx
    simpa only [Int.cast_natCast] using sawtooth_affine
      (n := (j/(N.factorial/(r+1)) : ℕ)) hb.1 hb.2
  unfold realBoundary cellBoundary cellIntercept
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [← twice_sum_indices]
  ring

theorem cell_boundary_continuous (N j : ℕ) : Continuous (cellBoundary N j) := by
  unfold cellBoundary
  fun_prop

/-- The polynomial at the left endpoint has the actual right-hand value. -/
theorem cell_left_endpoint (N j : ℕ) :
    cellBoundary N j (grid N.factorial j)=
      realBoundary N (grid N.factorial j)-(halfJump N (grid N.factorial j) : ℝ) := by
  have hq : Tendsto (cellBoundary N j) (𝓝[>] (grid N.factorial j))
      (𝓝 (cellBoundary N j (grid N.factorial j))) :=
    (cell_boundary_continuous N j).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : realBoundary N =ᶠ[𝓝[>] (grid N.factorial j)] cellBoundary N j := by
    filter_upwards [Ioo_mem_nhdsGT (grid_step (Nat.factorial_pos N) j)] with x hx
    exact boundary_on_cell N j hx
  exact tendsto_nhds_unique hq ((boundary_right N (grid N.factorial j)).congr' he)

/-- The polynomial at the right endpoint has the actual left-hand value. -/
theorem cell_right_endpoint (N j : ℕ) :
    cellBoundary N j (grid N.factorial (j+1))=
      realBoundary N (grid N.factorial (j+1))+(halfJump N (grid N.factorial (j+1)) : ℝ) := by
  have hq : Tendsto (cellBoundary N j) (𝓝[<] (grid N.factorial (j+1)))
      (𝓝 (cellBoundary N j (grid N.factorial (j+1)))) :=
    (cell_boundary_continuous N j).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : realBoundary N =ᶠ[𝓝[<] (grid N.factorial (j+1))] cellBoundary N j := by
    filter_upwards [Ioo_mem_nhdsLT (grid_step (Nat.factorial_pos N) j)] with x hx
    exact boundary_on_cell N j hx
  exact tendsto_nhds_unique hq ((boundary_left N (grid N.factorial (j+1))).congr' he)

end NField.Alignment.RealBoundaryUniformCells
