/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CollisionDedekindPairing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Actual one-sided limits and derivatives of the midpoint sawtooth -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealSawtoothLimits
open scoped Topology
open Filter Set CollisionDedekindPairing

theorem sawtooth_affine {n : ℤ} {x : ℝ} (hleft : (n : ℝ) < x) (hright : x < n+1) :
    periodicSawtooth x=x-n-1/2 := by
  have hf : Int.floor x=n := Int.floor_eq_iff.mpr ⟨hleft.le,hright⟩
  have hne : Int.fract x ≠ 0 := by unfold Int.fract; rw [hf]; linarith
  rw [periodicSawtooth, if_neg hne]
  simp only [Int.fract,hf]

theorem fract_ne_on_cell {n : ℤ} {x : ℝ} (hleft : (n : ℝ) < x) (hright : x < n+1) :
    Int.fract x ≠ 0 := by
  have hf : Int.floor x=n := Int.floor_eq_iff.mpr ⟨hleft.le,hright⟩
  unfold Int.fract
  rw [hf]
  linarith

theorem eventually_fract_ne_left (x : ℝ) : ∀ᶠ y in 𝓝[<] x, Int.fract y ≠ 0 := by
  by_cases hx : Int.fract x=0
  · have he : x=(Int.floor x : ℝ) := by unfold Int.fract at hx; linarith
    rw [he]
    filter_upwards [Ioo_mem_nhdsLT (show (Int.floor x : ℝ)-1<Int.floor x by linarith)] with y hy
    exact fract_ne_on_cell (n := Int.floor x-1) (by push_cast; exact hy.1)
      (by push_cast; linarith [hy.2])
  · have hn : x ≠ (Int.floor x : ℝ) := by intro h; apply hx; unfold Int.fract; linarith
    exact ((continuousAt_fract hn).eventually_ne hx).filter_mono nhdsWithin_le_nhds

theorem eventually_fract_ne_right (x : ℝ) : ∀ᶠ y in 𝓝[>] x, Int.fract y ≠ 0 := by
  by_cases hx : Int.fract x=0
  · have he : x=(Int.floor x : ℝ) := by unfold Int.fract at hx; linarith
    rw [he]
    filter_upwards [Ioo_mem_nhdsGT (show (Int.floor x : ℝ)<Int.floor x+1 by linarith)] with y hy
    exact fract_ne_on_cell hy.1 hy.2
  · have hn : x ≠ (Int.floor x : ℝ) := by intro h; apply hx; unfold Int.fract; linarith
    exact ((continuousAt_fract hn).eventually_ne hx).filter_mono nhdsWithin_le_nhds

theorem sawtooth_deriv {x : ℝ} (hx : Int.fract x ≠ 0) :
    HasDerivAt periodicSawtooth 1 x := by
  have hleft : (Int.floor x : ℝ) < x := by
    have := Int.floor_le x
    unfold Int.fract at hx
    exact lt_of_le_of_ne this (by intro h; exact hx (by linarith))
  have hright := Int.lt_floor_add_one x
  have h : HasDerivAt (fun y : ℝ => y-(Int.floor x : ℝ)-1/2) 1 x := by
    simpa using ((hasDerivAt_id x).sub_const (Int.floor x : ℝ)).sub_const (1/2 : ℝ)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hleft hright] with y hy
  exact sawtooth_affine hy.1 hy.2

theorem sawtooth_left_integer (n : ℤ) :
    Tendsto periodicSawtooth (𝓝[<] (n : ℝ)) (𝓝 (1/2)) := by
  have ht : Tendsto (fun y : ℝ => y-((n : ℝ)-1)-1/2)
      (𝓝[<] (n : ℝ)) (𝓝 (1/2)) := by
    have hbase : Tendsto (fun y : ℝ => y) (𝓝[<] (n : ℝ)) (𝓝 (n : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [show (n : ℝ)-((n : ℝ)-1)-1/2=1/2 by ring] using
      (hbase.sub_const ((n : ℝ)-1)).sub_const (1/2 : ℝ)
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (n : ℝ)-1<n by linarith)] with y hy
  have h := sawtooth_affine (n := n-1) (by push_cast; exact hy.1) (by push_cast; linarith [hy.2])
  push_cast at h
  exact h.symm

theorem sawtooth_right_integer (n : ℤ) :
    Tendsto periodicSawtooth (𝓝[>] (n : ℝ)) (𝓝 (-1/2)) := by
  have ht : Tendsto (fun y : ℝ => y-(n : ℝ)-1/2)
      (𝓝[>] (n : ℝ)) (𝓝 (-1/2)) := by
    have hbase : Tendsto (fun y : ℝ => y) (𝓝[>] (n : ℝ)) (𝓝 (n : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self,zero_sub,neg_div] using
      (hbase.sub_const (n : ℝ)).sub_const (1/2 : ℝ)
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ)<n+1 by linarith)] with y hy
  exact (sawtooth_affine hy.1 hy.2).symm

theorem sawtooth_left (x : ℝ) :
    Tendsto periodicSawtooth (𝓝[<] x)
      (𝓝 (periodicSawtooth x+if Int.fract x=0 then 1/2 else 0)) := by
  by_cases hx : Int.fract x=0
  · have he : x=(Int.floor x : ℝ) := by unfold Int.fract at hx; linarith
    rw [if_pos hx,periodicSawtooth,if_pos hx,zero_add,he]
    exact sawtooth_left_integer _
  · simpa only [if_neg hx,add_zero] using (sawtooth_deriv hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem sawtooth_right (x : ℝ) :
    Tendsto periodicSawtooth (𝓝[>] x)
      (𝓝 (periodicSawtooth x-if Int.fract x=0 then 1/2 else 0)) := by
  by_cases hx : Int.fract x=0
  · have he : x=(Int.floor x : ℝ) := by unfold Int.fract at hx; linarith
    rw [if_pos hx,periodicSawtooth,if_pos hx,zero_sub,he]
    simpa only [neg_div] using sawtooth_right_integer (Int.floor x)
  · simpa only [if_neg hx,sub_zero] using (sawtooth_deriv hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end NField.Alignment.RealSawtoothLimits
