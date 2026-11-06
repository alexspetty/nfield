/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedCells

/-! # The actual weighted profile has the printed weak second derivative on the circle -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedDistribution

open scoped BigOperators
open Set MeasureTheory CollisionRampEnergy CommonResetGram CommonResetWeightedSampling
open CommonResetWeightedCells

theorem weighted_square_integrable (N : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => weightedProfile N c x^2) volume a b := by
  simp only [weightedProfile_square]
  apply IntervalIntegrable.const_mul
  have hint (j k : ℕ) (hj : j ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => (c j*c k)*(midpointRow j x*midpointRow k x)) volume a b :=
    (midpointProduct_intervalIntegrable (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hk).1 a b).const_mul _
  exact ⟨integrable_finsetSum _ (fun j hj => integrable_finsetSum _ (fun k hk => (hint j k hj hk).1)),
    integrable_finsetSum _ (fun j hj => integrable_finsetSum _ (fun k hk => (hint j k hj hk).2))⟩

theorem weighted_square_test_integrable (N : ℕ) (c : ℕ → ℝ) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (a b : ℝ) :
    IntervalIntegrable (fun x => (weightedProfile N c x^2 : ℂ)*φ x) volume a b := by
  have hf := weighted_square_integrable N c a b
  exact (show IntervalIntegrable (fun x => (weightedProfile N c x^2 : ℂ)) volume a b
    from ⟨by
      unfold IntegrableOn
      convert! (hf.1.ofReal (𝕜 := ℂ)) using 1 <;> norm_cast,
      by
      unfold IntegrableOn
      convert! (hf.2.ofReal (𝕜 := ℂ)) using 1 <;> norm_cast⟩).mul_continuousOn hφ.continuousOn

theorem cellProfile_continuous (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    Continuous (cellProfile N D c k) :=
  continuous_iff_continuousAt.mpr (fun x => (cellProfile_derivative N D c k x).continuousAt)

def cellBoundary (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) (φ φ' : ℝ → ℂ) (x : ℝ) : ℂ :=
  (cellProfile N D c k x : ℂ)^2*φ' x-
    2*(2*slopeMoment N c : ℝ)*(cellProfile N D c k x : ℂ)*φ x

theorem cell_integration_by_parts (N D : ℕ) (c : ℕ → ℝ) (k : ℕ)
    (φ φ' φ'' : ℝ → ℂ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x) (hφ'' : Continuous φ'') (a b : ℝ) :
    (∫ x in a..b, (cellProfile N D c k x : ℂ)^2*φ'' x) =
      cellBoundary N D c k φ φ' b-cellBoundary N D c k φ φ' a+
        (2*(2*slopeMoment N c)^2 : ℝ)*∫ x in a..b, φ x := by
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hP := cellProfile_continuous N D c k
  have hderiv (x : ℝ) : HasDerivAt (cellBoundary N D c k φ φ')
      ((cellProfile N D c k x : ℂ)^2*φ'' x-(2*(2*slopeMoment N c)^2 : ℝ)*φ x) x := by
    have hd := (cellProfile_derivative N D c k x).ofReal_comp
    convert! ((hd.pow 2).mul (hφ' x)).sub
      (((hd.const_mul (2*(2*slopeMoment N c : ℝ) : ℂ))).mul (hφ x)) using 1 <;>
      simp only [cellBoundary, Pi.pow_apply] <;> push_cast <;> norm_num <;> ring
  have hi1 : IntervalIntegrable (fun x => (cellProfile N D c k x : ℂ)^2*φ'' x) volume a b :=
    ((Complex.continuous_ofReal.comp hP).pow 2 |>.mul hφ'').intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun x => (2*(2*slopeMoment N c)^2 : ℝ)*φ x) volume a b :=
    (hcont.const_mul _).intervalIntegrable a b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at he
  linear_combination he

theorem weightedProfile_zero (N : ℕ) (c : ℕ → ℝ) : weightedProfile N c 0=0 := by
  simp [weightedProfile, midpointRow]

theorem weightedProfile_one (N : ℕ) (c : ℕ → ℝ) : weightedProfile N c 1=0 := by
  simp [weightedProfile, midpointRow]

theorem gridReset_period {N D : ℕ} (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ) :
    gridReset N D c D=gridReset N D c 0 := by
  unfold gridReset
  apply Finset.sum_congr rfl
  intro j hj
  have hd : D/j ∣ D := ⟨j, (Nat.div_mul_cancel (hdiv j hj)).symm⟩
  simp [Nat.mod_eq_zero_of_dvd hd]

theorem shifted_boundary_sum (D : ℕ) (f g : ℕ → ℂ) :
    (∑ k ∈ Finset.range D, (f (k+1)-g k)) =
      (∑ k ∈ Finset.range D, (f k-g k))+f D-f 0 := by
  induction D with
  | zero => simp
  | succ D ih => simp only [Finset.sum_range_succ, ih]; ring

def valueJump (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -4*gridReset N D c k*weightedProfile N c ((k : ℝ)/D)

def slopeJump (N D : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -4*(2*slopeMoment N c)*gridReset N D c k

/-- Title: `The actual weighted clock square has exactly its printed distributional second derivative on the circle`. -/
theorem weighted_circle_second_derivative {N D : ℕ} (hD : 0 < D)
    (hdiv : ∀ j ∈ Finset.Icc 1 N, j ∣ D) (c : ℕ → ℝ)
    (φ φ' φ'' : ℝ → ℂ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x) (hφ'' : Continuous φ'')
    (hperiod : φ 1=φ 0) (hperiod' : φ' 1=φ' 0) :
    (∫ x in (0 : ℝ)..1, (weightedProfile N c x^2 : ℂ)*φ'' x) =
      (2*(2*slopeMoment N c)^2 : ℝ)*(∫ x in (0 : ℝ)..1, φ x)+
        ∑ k ∈ Finset.range D, ((slopeJump N D c k : ℂ)*φ ((k : ℝ)/D)-
          (valueJump N D c k : ℂ)*φ' ((k : ℝ)/D)) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  let plus : ℕ → ℂ := fun k =>
    ((weightedProfile N c ((k : ℝ)/D)+gridReset N D c k : ℝ) : ℂ)^2*φ' ((k : ℝ)/D)-
      2*(2*slopeMoment N c : ℝ)*
        ((weightedProfile N c ((k : ℝ)/D)+gridReset N D c k : ℝ) : ℂ)*φ ((k : ℝ)/D)
  let minus : ℕ → ℂ := fun k =>
    ((weightedProfile N c ((k : ℝ)/D)-gridReset N D c k : ℝ) : ℂ)^2*φ' ((k : ℝ)/D)-
      2*(2*slopeMoment N c : ℝ)*
        ((weightedProfile N c ((k : ℝ)/D)-gridReset N D c k : ℝ) : ℂ)*φ ((k : ℝ)/D)
  have hp : plus D=plus 0 := by
    dsimp [plus]
    simp only [div_self hDR, Nat.cast_zero, zero_div, weightedProfile_zero, weightedProfile_one,
      gridReset_period hdiv c, hperiod, hperiod']
  have hlocal (k : ℕ) :
      (∫ x in (k : ℝ)/D..((k+1 : ℕ) : ℝ)/D, (weightedProfile N c x^2 : ℂ)*φ'' x) =
        plus (k+1)-minus k+(2*(2*slopeMoment N c)^2 : ℝ)*
          ∫ x in (k : ℝ)/D..((k+1 : ℕ) : ℝ)/D, φ x := by
    have he : (∫ x in (k : ℝ)/D..((k+1 : ℕ) : ℝ)/D,
        (weightedProfile N c x^2 : ℂ)*φ'' x) =
      ∫ x in (k : ℝ)/D..((k+1 : ℕ) : ℝ)/D, (cellProfile N D c k x : ℂ)^2*φ'' x := by
      apply intervalIntegral.integral_congr_Ioo_of_le
        (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (Nat.cast_nonneg D))
      intro x hx
      dsimp only
      rw [weightedProfile_on_common_cell hD hdiv c k (by simpa only [Nat.cast_add, Nat.cast_one] using hx)]
    rw [he, cell_integration_by_parts N D c k φ φ' φ'' hφ hφ' hφ'']
    dsimp only [cellBoundary]
    rw [cell_right_value hD hdiv c k]
    simp only [Nat.cast_add, Nat.cast_one, cell_left_value hD hdiv c k, plus, minus]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ)/D) (n := D)
    (fun k _ => weighted_square_test_integrable N c hφ'' _ _)
  have hsumφ := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ)/D) (n := D) (f := φ) (μ := volume)
    (fun k _ => hcont.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div, div_self hDR] at hsum hsumφ
  rw [← hsum]
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ, shifted_boundary_sum, hp]
  have hterms : (∑ k ∈ Finset.range D, (plus k-minus k)) =
      ∑ k ∈ Finset.range D, ((slopeJump N D c k : ℂ)*φ ((k : ℝ)/D)-
        (valueJump N D c k : ℂ)*φ' ((k : ℝ)/D)) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [plus, minus, slopeJump, valueJump]
    push_cast
    ring
  rw [hterms]
  ring

end NField.Alignment.CommonResetWeightedDistribution
