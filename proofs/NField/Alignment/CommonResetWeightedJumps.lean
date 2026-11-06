/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedDistribution

/-! # Actual one-sided limits and value and slope jumps of the weighted profile -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedJumps

open scoped BigOperators Topology
open Set Filter CollisionRampEnergy CommonResetGram CommonResetWeightedSampling
open CommonResetWeightedSources CommonResetWeightedCells CommonResetWeightedDistribution

theorem common_cell_strict {D : ℕ} (hD : 0 < D) (k : ℕ) :
    (k : ℝ)/D<((k : ℝ)+1)/D := by
  exact div_lt_div_of_pos_right (by linarith) (by exact_mod_cast hD)

/-- Title: `The actual weighted profile has the prescribed right limit at every common-grid reset`. -/
theorem weighted_right_limit {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ) :
    Tendsto (weightedProfile N c) (𝓝[>] ((k : ℝ)/D))
      (𝓝 (weightedProfile N c ((k : ℝ)/D)-gridReset N D c k)) := by
  have hc := (cellProfile_continuous N D c k).continuousAt.tendsto.mono_left
    (show 𝓝[>] ((k : ℝ)/D) ≤ 𝓝 ((k : ℝ)/D) from nhdsWithin_le_nhds)
  rw [cell_right_value hD hdiv c k] at hc
  apply hc.congr'
  have hhi : Iio (((k : ℝ)+1)/D) ∈ 𝓝[>] ((k : ℝ)/D) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (common_cell_strict hD k))
  filter_upwards [self_mem_nhdsWithin, hhi] with x hx hy
  exact (weightedProfile_on_common_cell hD hdiv c k ⟨hx, hy⟩).symm

/-- Title: `The actual weighted profile has the prescribed left limit at every common-grid reset`. -/
theorem weighted_left_limit {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ) :
    Tendsto (weightedProfile N c) (𝓝[<] (((k : ℝ)+1)/D))
      (𝓝 (weightedProfile N c (((k : ℝ)+1)/D)+gridReset N D c (k+1))) := by
  have hc := (cellProfile_continuous N D c k).continuousAt.tendsto.mono_left
    (show 𝓝[<] (((k : ℝ)+1)/D) ≤ 𝓝 (((k : ℝ)+1)/D) from nhdsWithin_le_nhds)
  rw [cell_left_value hD hdiv c k] at hc
  apply hc.congr'
  have hlo : Ioi ((k : ℝ)/D) ∈ 𝓝[<] (((k : ℝ)+1)/D) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (common_cell_strict hD k))
  filter_upwards [self_mem_nhdsWithin, hlo] with x hx hy
  exact (weightedProfile_on_common_cell hD hdiv c k ⟨hy, hx⟩).symm

/-- Title: `Squaring the actual weighted one-sided readings gives the printed value jump and midpoint correction`. -/
theorem weighted_squared_jump (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    (weightedProfile N c ((k : ℝ)/D)-gridReset N D c k)^2-
      (weightedProfile N c ((k : ℝ)/D)+gridReset N D c k)^2=valueJump N D c k ∧
    ((weightedProfile N c ((k : ℝ)/D)-gridReset N D c k)^2+
      (weightedProfile N c ((k : ℝ)/D)+gridReset N D c k)^2)/2=
      weightedProfile N c ((k : ℝ)/D)^2+(gridReset N D c k)^2 := by
  unfold valueJump
  constructor <;> ring

/-- Title: `The derivatives of the actual squared affine cells have precisely the printed slope jump`. -/
theorem weighted_squared_slope_jump (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    2*(2*slopeMoment N c)*(weightedProfile N c ((k : ℝ)/D)-gridReset N D c k)-
      2*(2*slopeMoment N c)*(weightedProfile N c ((k : ℝ)/D)+gridReset N D c k)=
        slopeJump N D c k := by
  unfold slopeJump
  ring

theorem squared_cell_derivative (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => cellProfile N D c k y^2)
      (2*(2*slopeMoment N c)*cellProfile N D c k x) x := by
  convert! (cellProfile_derivative N D c k x).pow 2 using 1 <;> norm_num <;> ring

def pointReset (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, if Int.fract ((j : ℝ)*x)=0 then c j else 0

theorem pointReset_grid {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) (k : ℕ) :
    pointReset N c ((k : ℝ)/D)=gridReset N D c k := by
  unfold pointReset gridReset
  apply Finset.sum_congr rfl
  intro j hj
  have hs := quotient_pos hD (Finset.mem_Icc.mp hj).1 (hdiv j hj)
  have ha := clock_argument (Finset.mem_Icc.mp hj).1 (hdiv j hj) k 0
  have hf := fract_affine_cell hs k (t := 0) (by norm_num) (by norm_num)
  simp only [add_zero] at ha hf
  rw [ha, hf]
  have hz : (((k%(D/j) : ℕ) : ℝ)/((D/j : ℕ) : ℝ)=0) ↔ k%(D/j)=0 := by
    rw [div_eq_zero_iff]
    simp [show ((D/j : ℕ) : ℝ) ≠ 0 by exact_mod_cast hs.ne']
  simp only [hz]

/-- Title: `The actual resetting clock mass at a reduced fraction equals its denominator weight`. -/
theorem pointReset_reduced {d : ℕ} (hd : 0 < d) (a : ℕ) (ha : a.Coprime d)
    (N : ℕ) (c : ℕ → ℝ) :
    pointReset N c ((a : ℝ)/d)=resetWeight N c d := by
  unfold pointReset resetWeight
  apply Finset.sum_congr rfl
  intro j hj
  have he : (j : ℝ)*((a : ℝ)/d)=(j*a : ℕ)/d := by push_cast; ring
  rw [he, Int.fract_div_natCast_eq_div_natCast_mod]
  have hz : ((((j*a)%d : ℕ) : ℝ)/(d : ℝ)=0) ↔ d ∣ j := by
    rw [div_eq_zero_iff]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [hdR, or_false, Nat.cast_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    exact ⟨fun h => ha.symm.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h a⟩
  simp only [hz]

end NField.Alignment.CommonResetWeightedJumps
