/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedJumps
import NField.Alignment.CommonResetGrid

/-! # Exact source illustrations at bases three and five -/

noncomputable section

namespace NField.Alignment.CommonResetSourceExamples

open scoped BigOperators Topology
open CommonResetGrid PrimeCarryTableColumnLaw CollisionRampEnergy DedekindReciprocity
open CommonResetWeightedJumps CommonResetWeightedCells CommonResetGram
open CommonResetWeightedDistribution Filter Set

theorem base_five_clock_set : Finset.Icc 1 4=({1, 2, 3, 4} : Finset ℕ) := by decide

/-- Title: `The base-three equal-digit marks and their doubled residues are exactly the stated lists`. -/
theorem base_three_marks :
    CollisionFluctuationSum.diagonalSlices 3=({0, 4, 8} : Finset ℕ) ∧
    (List.range 3).map (fun d => (2*((3+1)*d))%(3^2))=[0, 8, 7] := by decide

/-- Title: `The base-three example has exactly two carries and centered reading four thirds`. -/
theorem base_three_example : carryThresholdCount 3 2=2 ∧ carryReading 3 2=4/3 := by
  have hc : carryThresholdCount 3 2=2 := by decide
  exact ⟨hc, by norm_num [carryReading, hc]⟩

theorem base_five_rational_reading (a : ℕ) :
    boundaryResponse 4 ((a : ℝ)/25)=
      2*∑ j ∈ Finset.Icc 1 4, (rationalSawtooth (j*a) 25 : ℝ) := by
  unfold boundaryResponse
  congr 1
  exact Finset.sum_congr rfl (fun j _ => midpointRow_rational (by norm_num : 0 < (25 : ℕ)) j a)

/-- Title: `The plotted base-five curve is exactly the squared affine clock profile to the right of zero`. -/
theorem base_five_right_curve {x : ℝ} (hx : 0 < x) (hxx : x < 1/12) :
    boundaryResponse 4 x^2=(4-20*x)^2 := by
  have hd : ∀ j ∈ Finset.Icc 1 4, j ∣ (12 : ℕ) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj4⟩
    interval_cases j <;> norm_num
  have he := weightedProfile_on_common_cell (N := 4) (by norm_num : 0 < (12 : ℕ)) hd
    (fun _ => (1 : ℝ)) 0 (x := x) (by simpa using And.intro hx hxx)
  rw [unit_weights] at he
  norm_num [cellProfile, cellClock, base_five_clock_set] at he
  rw [he]
  ring

/-- Title: `The plotted base-five curve is exactly the squared affine clock profile to the left of zero`. -/
theorem base_five_left_curve {x : ℝ} (hx : -(1/12 : ℝ) < x) (hxx : x < 0) :
    boundaryResponse 4 x^2=(4+20*x)^2 := by
  have hd : ∀ j ∈ Finset.Icc 1 4, j ∣ (12 : ℕ) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj4⟩
    interval_cases j <;> norm_num
  have he := weightedProfile_on_common_cell (N := 4) (by norm_num : 0 < (12 : ℕ)) hd
    (fun _ => (1 : ℝ)) 11 (x := x+1) (by constructor <;> norm_num <;> linarith)
  rw [unit_weights, boundaryResponse_periodic 4 x] at he
  norm_num [cellProfile, cellClock, base_five_clock_set] at he
  rw [he]
  ring

/-- Title: `The base-five squared profile has the plotted one-sided limit sixteen at its common reset`. -/
theorem base_five_right_limit :
    Filter.Tendsto (fun x => boundaryResponse 4 x^2) (𝓝[>] (0 : ℝ)) (𝓝 16) := by
  have hd : ∀ j ∈ Finset.Icc 1 4, j ∣ (12 : ℕ) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj4⟩
    interval_cases j <;> norm_num
  have he := weighted_right_limit (N := 4) (by norm_num : 0 < (12 : ℕ)) hd
    (fun _ => (1 : ℝ)) 0
  simp only [Nat.cast_zero, zero_div, weightedProfile_zero, unit_weights] at he
  norm_num [gridReset, base_five_clock_set] at he
  convert he.pow 2 using 1 <;> norm_num

/-- Title: `The base-five squared profile has the same limit sixteen from the left of the common reset`. -/
theorem base_five_left_limit :
    Tendsto (fun x => boundaryResponse 4 x^2) (𝓝[<] (0 : ℝ)) (𝓝 16) := by
  have hd : ∀ j ∈ Finset.Icc 1 4, j ∣ (12 : ℕ) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj4⟩
    interval_cases j <;> norm_num
  have he := weighted_left_limit (N := 4) (by norm_num : 0 < (12 : ℕ)) hd
    (fun _ => (1 : ℝ)) 11
  norm_num only [Nat.cast_ofNat, show ((11 : ℝ)+1)/12=1 by norm_num,
    weightedProfile_one, unit_weights] at he
  norm_num [gridReset, base_five_clock_set] at he
  have hcount : ({x ∈ ({1, 2, 3, 4} : Finset ℕ) | 12 % (12/x)=0}).card=4 := by decide
  norm_num only [hcount, Nat.cast_ofNat] at he
  have ht : Tendsto (fun x : ℝ => x+1) (𝓝[<] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun x : ℝ => x) (𝓝[<] 0) (𝓝 0) :=
        continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [zero_add] using hid.add_const 1
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x+1<1
      change x<0 at hx
      linarith
  have hf := (he.comp ht).pow 2
  have hp (x : ℝ) : boundaryResponse 4 (x+1)=boundaryResponse 4 x := boundaryResponse_periodic 4 x
  simpa only [Function.comp_apply, hp, show (4 : ℝ)^2=16 by norm_num] using hf

/-- Title: `All five plotted base-five grid squares have their exact stated values`. -/
theorem base_five_figure_samples :
    boundaryResponse 4 (-(2/25 : ℝ))^2=144/25 ∧
    boundaryResponse 4 (-(1/25 : ℝ))^2=256/25 ∧
    boundaryResponse 4 0^2=0 ∧
    boundaryResponse 4 (1/25)^2=256/25 ∧
    boundaryResponse 4 (2/25)^2=144/25 := by
  have hn1 := boundaryResponse_periodic 4 (-(1/25 : ℝ))
  have hn2 := boundaryResponse_periodic 4 (-(2/25 : ℝ))
  norm_num at hn1 hn2
  rw [← hn1, ← hn2]
  norm_num [base_five_rational_reading, boundaryResponse, midpointRow,
    affineRow, rationalSawtooth, Finset.sum_Icc_succ_top]

/-- Title: `Replacing the plotted origin by its one-sided square raises the grid average by sixteen twenty-fifths`. -/
theorem base_five_origin_correction :
    ((∑ a ∈ Finset.range 25,
        if a=0 then (16 : ℝ) else boundaryResponse 4 ((a : ℝ)/25)^2)/25)-
      (∑ a ∈ Finset.range 25, boundaryResponse 4 ((a : ℝ)/25)^2)/25=16/25 := by
  have hp (a : ℕ) :
      (if a=0 then (16 : ℝ) else boundaryResponse 4 ((a : ℝ)/25)^2)=
        boundaryResponse 4 ((a : ℝ)/25)^2+(if a=0 then 16 else 0) := by
    by_cases ha : a=0
    · subst a
      simp [boundaryResponse, midpointRow]
    · simp [ha]
  simp only [hp, Finset.sum_add_distrib]
  norm_num
  ring

end NField.Alignment.CommonResetSourceExamples
