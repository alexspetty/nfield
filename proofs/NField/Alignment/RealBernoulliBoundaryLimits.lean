/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothLimits
import NField.Alignment.CarrierJumpData
import Mathlib.Data.Nat.Factorization.Basic

/-! # One-sided limits of the actual real Bernoulli boundary -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealBernoulliBoundaryLimits
open scoped BigOperators Topology
open Filter Set CollisionDedekindPairing RealSawtoothLimits CarrierJumpData DedekindReciprocity

def realBoundary (N : ℕ) (x : ℝ) : ℝ :=
  2*∑ r ∈ Finset.range N, periodicSawtooth (((r+1 : ℕ) : ℝ)*x)
def halfJump (N : ℕ) (x : ℝ) : ℕ :=
  ((Finset.range N).filter fun r => Int.fract (((r+1 : ℕ) : ℝ)*x)=0).card

theorem positive_mul_left_limit {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Tendsto (fun y => r*y) (𝓝[<] x) (𝓝[<] (r*x)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (continuousAt_const.mul continuousAt_id).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_lt_mul_of_pos_left hy hr

theorem positive_mul_right_limit {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Tendsto (fun y => r*y) (𝓝[>] x) (𝓝[>] (r*x)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (continuousAt_const.mul continuousAt_id).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_lt_mul_of_pos_left hy hr

theorem sum_half_indicators (N : ℕ) (x : ℝ) :
    (∑ r ∈ Finset.range N, if Int.fract (((r+1 : ℕ) : ℝ)*x)=0 then (1/2 : ℝ) else 0) =
      (halfJump N x : ℝ)/2 := by
  rw [← Finset.sum_filter]
  simp [halfJump]
  ring

theorem boundary_left (N : ℕ) (x : ℝ) :
    Tendsto (realBoundary N) (𝓝[<] x) (𝓝 (realBoundary N x+(halfJump N x : ℝ))) := by
  have h := tendsto_finsetSum (Finset.range N) fun r hr =>
    (sawtooth_left (((r+1 : ℕ) : ℝ)*x)).comp
      (positive_mul_left_limit (by positivity : (0 : ℝ)<((r+1 : ℕ) : ℝ)) x)
  have ht := h.const_mul 2
  rw [Finset.sum_add_distrib,sum_half_indicators] at ht
  change Tendsto (realBoundary N) (𝓝[<] x)
    (𝓝 (2*((∑ r ∈ Finset.range N,periodicSawtooth (((r+1 : ℕ) : ℝ)*x))+(halfJump N x : ℝ)/2))) at ht
  have he : 2*((∑ r ∈ Finset.range N,periodicSawtooth (((r+1 : ℕ) : ℝ)*x))+(halfJump N x : ℝ)/2) =
    realBoundary N x+(halfJump N x : ℝ) := by unfold realBoundary; ring
  rwa [he] at ht

theorem boundary_right (N : ℕ) (x : ℝ) :
    Tendsto (realBoundary N) (𝓝[>] x) (𝓝 (realBoundary N x-(halfJump N x : ℝ))) := by
  have h := tendsto_finsetSum (Finset.range N) fun r hr =>
    (sawtooth_right (((r+1 : ℕ) : ℝ)*x)).comp
      (positive_mul_right_limit (by positivity : (0 : ℝ)<((r+1 : ℕ) : ℝ)) x)
  have ht := h.const_mul 2
  rw [Finset.sum_sub_distrib,sum_half_indicators] at ht
  change Tendsto (realBoundary N) (𝓝[>] x)
    (𝓝 (2*((∑ r ∈ Finset.range N,periodicSawtooth (((r+1 : ℕ) : ℝ)*x))-(halfJump N x : ℝ)/2))) at ht
  have he : 2*((∑ r ∈ Finset.range N,periodicSawtooth (((r+1 : ℕ) : ℝ)*x))-(halfJump N x : ℝ)/2) =
    realBoundary N x-(halfJump N x : ℝ) := by unfold realBoundary; ring
  rwa [he] at ht

theorem sawtooth_rational (a k : ℕ) (hk : 0 < k) :
    periodicSawtooth ((a : ℝ)/k)=(rationalSawtooth a k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hzero : ((a%k : ℕ) : ℝ)/(k : ℝ)=0 ↔ a%k=0 := by simp [div_eq_zero_iff,hkR]
  unfold periodicSawtooth rationalSawtooth
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  simp only [hzero]
  by_cases h : a%k=0 <;> simp [h]

theorem boundary_rational {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    realBoundary N ((a : ℝ)/k)=(cyclicPrefixResponse a k (N%k) : ℝ) := by
  rw [← boundaryMidpoint_eq_cyclicPrefix hk hcop]
  unfold realBoundary boundaryMidpoint
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_div_assoc] using
    sawtooth_rational ((r+1)*a) k hk

theorem halfJump_rational {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    halfJump N ((a : ℝ)/k)=N/k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold halfJump
  convert Nat.card_multiples N k using 1
  congr 1
  ext r
  simp only [Finset.mem_filter]
  congr 1
  rw [← mul_div_assoc, ← Nat.cast_mul,Int.fract_div_natCast_eq_div_natCast_mod]
  rw [div_eq_zero_iff]
  simp only [hkR,or_false,Nat.cast_eq_zero,← Nat.dvd_iff_mod_eq_zero,
    hcop.symm.dvd_mul_right]

/-- Title: `The actual one-sided boundary values at a reduced rational point`. -/
theorem rational_boundary_limits {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    Tendsto (realBoundary N) (𝓝[<] ((a : ℝ)/k))
      (𝓝 ((cyclicPrefixResponse a k (N%k) : ℝ)+(N/k : ℕ))) ∧
    Tendsto (realBoundary N) (𝓝[>] ((a : ℝ)/k))
      (𝓝 ((cyclicPrefixResponse a k (N%k) : ℝ)-(N/k : ℕ))) := by
  constructor
  · simpa only [boundary_rational hk hcop,halfJump_rational hk hcop] using boundary_left N ((a : ℝ)/k)
  · simpa only [boundary_rational hk hcop,halfJump_rational hk hcop] using boundary_right N ((a : ℝ)/k)

/-- Title: `The actual boundary values at the origin`. -/
theorem origin_boundary_limits (N : ℕ) :
    realBoundary N 0=0 ∧ Tendsto (realBoundary N) (𝓝[<] 0) (𝓝 (N : ℝ)) ∧
      Tendsto (realBoundary N) (𝓝[>] 0) (𝓝 (-(N : ℝ))) := by
  have hb : realBoundary N 0=0 := by simp [realBoundary,periodicSawtooth]
  have hj : halfJump N 0=N := by simp [halfJump]
  exact ⟨hb,by simpa [hb,hj] using boundary_left N 0,by simpa [hb,hj] using boundary_right N 0⟩

end NField.Alignment.RealBernoulliBoundaryLimits
