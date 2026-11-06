/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BernoulliFourierIdentity
import NField.Alignment.RealSawtoothDistribution

/-! # Exact symmetric smoothing of the real sawtooth -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliSymmetricSmoothing
open scoped Classical
open RealCarrierGridAlias CollisionDedekindPairing RealSawtoothDistribution

def smoothedSaw (δ y : ℝ) : ℝ :=
  (bernoulliTwo (y+δ)-bernoulliTwo (y-δ))/(4*δ)

theorem bernoulliTwo_add_one (x : ℝ) : bernoulliTwo (x+1)=bernoulliTwo x := by
  simp [bernoulliTwo,Int.fract_add_one]

theorem bernoulliTwo_sub_one (x : ℝ) : bernoulliTwo (x-1)=bernoulliTwo x := by
  simp [bernoulliTwo,Int.fract_sub_one]

theorem bernoulliTwo_closed_interval {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    bernoulliTwo x=x^2-x+1/6 := by
  rcases hx1.lt_or_eq with hlt | rfl
  · simp only [bernoulliTwo,Int.fract_eq_self.mpr ⟨hx,hlt⟩]
  · norm_num [bernoulliTwo]

theorem smoothedSaw_fract (δ y : ℝ) : smoothedSaw δ y=smoothedSaw δ (Int.fract y) := by
  have h (t : ℝ) : Int.fract (y+t)=Int.fract (Int.fract y+t) := by
    have he : y+t=(Int.fract y+t)+(⌊y⌋ : ℤ) := by
      linarith [Int.fract_add_floor y]
    rw [he,Int.fract_add_intCast]
  simp only [smoothedSaw,bernoulliTwo,sub_eq_add_neg,h]

theorem smoothed_central {δ u : ℝ} (hδ : 0 < δ) (hu : δ ≤ u) (hu1 : u ≤ 1-δ) :
    smoothedSaw δ u=u-1/2 := by
  rw [smoothedSaw,bernoulliTwo_closed_interval (by linarith) (by linarith),
    bernoulliTwo_closed_interval (by linarith) (by linarith)]
  field_simp
  ring

theorem smoothed_left {δ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hu : 0 ≤ u) (huδ : u ≤ δ) :
    smoothedSaw δ u= -(1-2*δ)*u/(2*δ) := by
  rw [smoothedSaw,← bernoulliTwo_add_one (u-δ),
    bernoulliTwo_closed_interval (by linarith) (by linarith),
    bernoulliTwo_closed_interval (by linarith) (by linarith)]
  field_simp
  ring

theorem smoothed_right {δ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hu : 1-δ ≤ u) (hu1 : u ≤ 1) :
    smoothedSaw δ u=(1-2*δ)*(1-u)/(2*δ) := by
  rw [smoothedSaw,← bernoulliTwo_sub_one (u+δ),
    bernoulliTwo_closed_interval (by linarith) (by linarith),
    bernoulliTwo_closed_interval (by linarith) (by linarith)]
  field_simp
  ring

/-- Symmetric smoothing retains the sawtooth's uniform half bound. -/
theorem smoothed_abs_le_half {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (y : ℝ) :
    |smoothedSaw δ y| ≤ 1/2 := by
  rw [smoothedSaw_fract]
  let u := Int.fract y
  have hu : 0 ≤ u := Int.fract_nonneg y
  have hu1 : u ≤ 1 := (Int.fract_lt_one y).le
  have hd : 0 < 2*δ := by positivity
  change |smoothedSaw δ u| ≤ _
  by_cases hlu : u ≤ δ
  · rw [smoothed_left hδ hδ1 hu hlu,abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hu) hd.le)]
    have hle : (1-2*δ)*u ≤ δ := by nlinarith
    have he : -(-(1-2*δ)*u/(2*δ))=(1-2*δ)*u/(2*δ) := by ring
    rw [he]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · by_cases hru : 1-δ ≤ u
    · rw [smoothed_right hδ hδ1 hru hu1,abs_of_nonneg (div_nonneg
        (mul_nonneg (by linarith) (by linarith)) hd.le)]
      apply (div_le_iff₀ hd).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ δ) (by linarith : 0 ≤ 1-u)]
    · rw [smoothed_central hδ (by linarith) (by linarith),abs_le]
      constructor <;> linarith

/-- Outside the short integer arc, smoothing changes no value at all. -/
theorem smoothed_eq_saw_of_no_arc {δ y : ℝ} (hδ : 0 < δ)
    (hfar : ¬∃ z : ℤ, |y-z| ≤ δ) : smoothedSaw δ y=periodicSawtooth y := by
  have hleft : δ < Int.fract y := by
    by_contra h
    apply hfar
    refine ⟨⌊y⌋,?_⟩
    change |Int.fract y| ≤ δ
    rw [abs_of_nonneg (Int.fract_nonneg y)]
    exact le_of_not_gt h
  have hright : Int.fract y < 1-δ := by
    by_contra h
    apply hfar
    refine ⟨⌊y⌋+1,?_⟩
    rw [Int.cast_add,Int.cast_one,show y-((⌊y⌋ : ℝ)+1)=Int.fract y-1 by rw [Int.fract]; ring,
      abs_of_nonpos (by linarith [Int.fract_lt_one y])]
    linarith
  rw [smoothedSaw_fract,smoothed_central hδ hleft.le hright.le]
  simp only [periodicSawtooth,if_neg (ne_of_gt (hδ.trans hleft))]

/-- The smoothing error is supported on the exact closed integer arc. -/
theorem smoothed_error_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (y : ℝ) :
    |periodicSawtooth y-smoothedSaw δ y| ≤
      if ∃ z : ℤ, |y-z| ≤ δ then 1 else 0 := by
  split_ifs with h
  · calc
      _ ≤ |periodicSawtooth y|+|smoothedSaw δ y| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          abs_add_le (periodicSawtooth y) (-smoothedSaw δ y)
      _ ≤ 1/2+1/2 := add_le_add (sawtooth_abs_bound y) (smoothed_abs_le_half hδ hδ1 y)
      _ = 1 := by norm_num
  · rw [smoothed_eq_saw_of_no_arc hδ h]
    simp

end NField.Alignment.BernoulliSymmetricSmoothing
