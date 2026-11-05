/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSieveApplications
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The exact main integral in the rough smoothing reduction

The finite windows are rearranged with their strict endpoints justified
by equality of Lebesgue interval integrals. The outer support is enlarged
only under a nonnegative squared integrand. The smooth sum vanishes beyond x.
The substitution z=x/t retains endpoints 1 and x/y and allows the
discontinuous smooth sum. Phase integrability is proved from the existing
fixed-support polynomial bounds. No Parseval or low-moment estimate is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperMainIntegral

open scoped BigOperators
open MeasureTheory Finset
open HarperSieveApplications HarperIntervalSieve HarperSmoothIntervals HarperSmoothCount
  HarperRoughSmoothing HarperSmoothRough SteinhausMoment

theorem short_window_iff {m t X : ℝ} (hX : 0 < X) :
    t/(1+1/X) < m ∧ m ≤ t ↔ m ≤ t ∧ t < m*(1+1/X) := by
  have hr : 0 < 1+1/X := by positivity
  rw [div_lt_iff₀ hr]
  exact and_comm

/-- The inverse substitution on the exact finite smoothing endpoints.
The monotone substitution theorem permits a discontinuous integrand. -/
theorem inverse_substitution (F : ℝ → ℝ) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (∫ t in y..x, F (x/t)) = x * ∫ z in (1 : ℝ)..x/y, F z / z^2 := by
  have hx : 0 < x := hy.trans_le hyx
  have hxy : 1 ≤ x/y := (le_div_iff₀ hy).mpr (by simpa using hyx)
  have hzpos : ∀ z ∈ Set.uIcc (1 : ℝ) (x/y), 0 < z := by
    intro z hz
    rw [Set.uIcc_of_le hxy, Set.mem_Icc] at hz
    linarith [hz.1]
  have hc : ContinuousOn (fun z : ℝ => x/z) (Set.uIcc 1 (x/y)) :=
    continuousOn_const.div continuousOn_id (fun z hz => (hzpos z hz).ne')
  have hd : ∀ z ∈ Set.Ioo (min (1 : ℝ) (x/y)) (max (1 : ℝ) (x/y)),
      HasDerivAt (fun z : ℝ => x/z) (-x/z^2) z := by
    intro z hz
    have hz0 : z ≠ 0 := (hzpos z ⟨hz.1.le, hz.2.le⟩).ne'
    simpa only [Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub] using!
      (hasDerivAt_const z x).div (hasDerivAt_id z) hz0
  have hn : ∀ z ∈ Set.Ioo (min (1 : ℝ) (x/y)) (max (1 : ℝ) (x/y)), -x/z^2 ≤ 0 := by
    intro z _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) (sq_nonneg z)
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun t : ℝ => F (x/t)) hc hd hn
  have he : (∫ z in (1 : ℝ)..x/y, ((fun t : ℝ => F (x/t)) ∘ (fun z : ℝ => x/z)) z * (-x/z^2)) =
      (-x) * ∫ z in (1 : ℝ)..x/y, F z / z^2 := by
    calc
      _ = ∫ z in (1 : ℝ)..x/y, (-x)*(F z/z^2) := by
        apply intervalIntegral.integral_congr
        intro z hz
        dsimp only [Function.comp_apply]
        have hi : x/(x/z) = z := by field_simp
        rw [hi]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hiy : x/(x/y) = y := by field_simp
  have hrev : (∫ t in x..y, F (x/t)) = - ∫ t in y..x, F (x/t) :=
    intervalIntegral.integral_symm y x
  rw [he, div_one, hiy, hrev] at hs
  linarith


/-- The finite window weight before enlarging the outer rough support. -/
def windowWeight (s : Finset ℕ) (X t : ℝ) : ℝ :=
  ∑ m ∈ s.filter (fun m : ℕ => t/(1+1/X) < (m : ℝ) ∧ (m : ℝ) ≤ t), X/(m : ℝ)

theorem windowWeight_nonneg (s : Finset ℕ) {X : ℝ} (hX : 0 ≤ X) (t : ℝ) :
    0 ≤ windowWeight s X t := sum_nonneg (fun _ _ => div_nonneg hX (Nat.cast_nonneg _))

theorem windowWeight_mul (s : Finset ℕ) {X : ℝ} (hX : 0 < X) (F : ℝ → ℝ) (t : ℝ) :
    windowWeight s X t * F t = ∑ m ∈ s,
      (Set.Ico (m : ℝ) ((m : ℝ)*(1+1/X))).indicator (fun t => X/(m : ℝ)*F t) t := by
  rw [windowWeight, sum_filter, sum_mul]
  apply sum_congr rfl
  intro m hm
  simp only [ite_mul, zero_mul, Set.indicator_apply, Set.mem_Ico, short_window_iff hX]

theorem windowWeight_le_roughShortWeight {X t : ℝ} (hX : 0 < X) (ht : 0 ≤ t)
    (x P y : ℝ) : windowWeight (roughAverageSupport ⌊x⌋₊ P y) X t ≤ roughShortWeight t P X := by
  have ha : 0 ≤ t/(1+1/X) := by positivity
  have hat : t/(1+1/X) ≤ t := by
    rw [short_lower_identity hX]
    exact (div_le_iff₀ (by linarith : 0 < X+1)).mpr (by nlinarith)
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rcases mem_filter.mp hm with ⟨hmR, hmI⟩
    have hmP := (mem_filter.mp hmR).2.2
    exact mem_filter.mpr ⟨(intervalSupport_mem ha hat m).mpr hmI, hmP⟩
  · intro m _ _
    exact div_nonneg hX.le (Nat.cast_nonneg m)

theorem integral_window_indicator (F : ℝ → ℝ) {y B m M : ℝ}
    (hyB : y ≤ B) (hmM : m ≤ M) (hsub : Set.Ico m M ⊆ Set.Ioc y B) :
    (∫ t in y..B, (Set.Ico m M).indicator F t) = ∫ t in m..M, F t := by
  rw [intervalIntegral.integral_of_le hyB, integral_indicator measurableSet_Ico,
    Measure.restrict_restrict_of_subset hsub, integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hmM]

theorem smoothSum_zero_of_lt_one {u P : ℝ} (hu : u < 1) (a : ℕ → ℂ) :
    smoothSum u P a = 0 := by
  have hs : smoothSet u P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    rcases smoothSet_mem.mp hn with ⟨hn0, hnu, _⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith
  simp only [smoothSum, hs, sum_empty]

theorem quotient_square_zero_past {x t P : ℝ} (hx : 0 ≤ x) (hxt : x < t)
    (a : ℕ → ℂ) : ‖smoothSum (x/t) P a‖^2 = 0 := by
  rw [smoothSum_zero_of_lt_one ((div_lt_one (hx.trans_lt hxt)).mpr hxt)]
  simp

theorem quotient_square_clip {x y B P : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hxB : x ≤ B)
    (a : ℕ → ℂ) :
    (∫ t in y..B, ‖smoothSum (x/t) P a‖^2) = ∫ t in y..x, ‖smoothSum (x/t) P a‖^2 := by
  have hx : 0 < x := hy.trans_le hyx
  have hzero : (∫ t in x..B, ‖smoothSum (x/t) P a‖^2) = 0 := by
    rw [intervalIntegral.integral_of_le hxB]
    apply integral_eq_zero_of_ae
    change ∀ᵐ t ∂volume.restrict (Set.Ioc x B), ‖smoothSum (x/t) P a‖^2 = 0
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun t ht => quotient_square_zero_past hx.le ht.1 a)
  have h := intervalIntegral.integral_add_adjacent_intervals
    (quotient_square_intervalIntegrable hx.le hy hyx (P := P) a)
    (quotient_square_intervalIntegrable hx.le hx hxB (P := P) a)
  simpa only [hzero, add_zero] using h.symm


private theorem rough_window_subset {x P y X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    {m : ℕ} (hm : m ∈ roughAverageSupport ⌊x⌋₊ P y) :
    Set.Ico (m : ℝ) ((m : ℝ)*(1+1/X)) ⊆ Set.Ioc y (x*(1+1/X)) := by
  rcases mem_filter.mp hm with ⟨hmI, hmy, _⟩
  have hmx : (m : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (mem_Icc.mp hmI).2
  intro t ht
  exact ⟨hmy.trans_le ht.1, ht.2.le.trans
    (mul_le_mul_of_nonneg_right hmx (by positivity))⟩

private theorem window_integrable {y B m X : ℝ} {F : ℝ → ℝ}
    (hf : IntervalIntegrable F volume y B) :
    IntervalIntegrable ((Set.Ico m (m*(1+1/X))).indicator (fun t => X/m*F t)) volume y B := by
  have h := hf.const_mul (X/m)
  exact ⟨h.1.indicator measurableSet_Ico, h.2.indicator measurableSet_Ico⟩

theorem rough_average_integral {x P y X : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hX : 0 < X) (a : ℕ → ℂ) :
    (∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, smoothAverage x P (m : ℝ) X a) =
      ∫ t in y..x*(1+1/X),
        windowWeight (roughAverageSupport ⌊x⌋₊ P y) X t * ‖smoothSum (x/t) P a‖^2 := by
  have hx : 0 < x := hy.trans_le hyx
  have hxB := smoothing_endpoint_le hx.le hX
  have hyB := hyx.trans hxB
  have hF := quotient_square_intervalIntegrable hx.le hy hyB (P := P) a
  calc
    _ = ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, ∫ t in y..x*(1+1/X),
        (Set.Ico (m : ℝ) ((m : ℝ)*(1+1/X))).indicator
          (fun t => X/(m : ℝ)*‖smoothSum (x/t) P a‖^2) t := by
      apply sum_congr rfl
      intro m hm
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [integral_window_indicator _ hyB (smoothing_endpoint_le hm0 hX)
        (rough_window_subset hx.le hX hm), intervalIntegral.integral_const_mul]
      rfl
    _ = ∫ t in y..x*(1+1/X), ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
        (Set.Ico (m : ℝ) ((m : ℝ)*(1+1/X))).indicator
          (fun t => X/(m : ℝ)*‖smoothSum (x/t) P a‖^2) t :=
      (intervalIntegral.integral_finsetSum (fun _ _ => window_integrable hF)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (windowWeight_mul _ hX _ t).symm

theorem sum_smoothAverage_le {x P y X C : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hX : 0 < X) (hshort : ∀ t : ℝ, y ≤ t → roughShortWeight t P X ≤ C) (a : ℕ → ℂ) :
    (∑ m ∈ roughAverageSupport ⌊x⌋₊ P y, smoothAverage x P (m : ℝ) X a) ≤
      C * ∫ t in y..x, ‖smoothSum (x/t) P a‖^2 := by
  have hx : 0 < x := hy.trans_le hyx
  have hxB := smoothing_endpoint_le hx.le hX
  have hyB := hyx.trans hxB
  have hF := quotient_square_intervalIntegrable hx.le hy hyB (P := P) a
  have hw : IntervalIntegrable (fun t =>
      windowWeight (roughAverageSupport ⌊x⌋₊ P y) X t * ‖smoothSum (x/t) P a‖^2)
      volume y (x*(1+1/X)) := by
    simp_rw [windowWeight_mul _ hX (fun t => ‖smoothSum (x/t) P a‖^2)]
    exact ⟨integrable_finsetSum _
        (fun m _ => (window_integrable (m := (m : ℝ)) (X := X) hF).1),
      integrable_finsetSum _
        (fun m _ => (window_integrable (m := (m : ℝ)) (X := X) hF).2)⟩
  rw [rough_average_integral hy hyx hX a]
  calc
    _ ≤ ∫ t in y..x*(1+1/X), C*‖smoothSum (x/t) P a‖^2 := by
      apply intervalIntegral.integral_mono_on hyB hw (hF.const_mul C)
      intro t ht
      exact mul_le_mul_of_nonneg_right
        ((windowWeight_le_roughShortWeight hX (hy.le.trans ht.1) x P y).trans (hshort t ht.1))
        (sq_nonneg _)
    _ = C * ∫ t in y..x, ‖smoothSum (x/t) P a‖^2 := by
      rw [intervalIntegral.integral_const_mul, quotient_square_clip hy hyx hxB a]

open HarperSmoothingMoment

/-- The actual unweighted smooth main integral, before inverse substitution. -/
def smoothMainIntegral (x P y : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ t in y..x, ‖smoothSum (x/t) P (fun n => steinhaus n ω)‖^2

/-- The exact finite inverse integral; its upper endpoint is x/y. -/
def smoothInverseIntegral (x P y : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ z in (1 : ℝ)..x/y, ‖smoothSum z P (fun n => steinhaus n ω)‖^2/z^2

theorem smoothMainIntegral_nonneg {x y : ℝ} (hyx : y ≤ x) (P : ℝ) (ω : PhaseSpace) :
    0 ≤ smoothMainIntegral x P y ω :=
  intervalIntegral.integral_nonneg hyx (fun _ _ => sq_nonneg _)

theorem smoothMainIntegral_eq_inverse {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (P : ℝ) (ω : PhaseSpace) :
    smoothMainIntegral x P y ω = x * smoothInverseIntegral x P y ω :=
  inverse_substitution (fun z => ‖smoothSum z P (fun n => steinhaus n ω)‖^2) hy hyx

theorem smoothMainIntegral_integrable {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (P : ℝ) :
    Integrable (smoothMainIntegral x P y) phaseMeasure := by
  have hx : 0 ≤ x := hy.le.trans hyx
  have heq (ω : PhaseSpace) : smoothMainIntegral x P y ω =
      ∫ t in y..x,
        ‖intervalPolynomial (smoothSet (x/y) P) (lowerCoefficient x (fun _ => 1)) (t,ω)‖^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    have hs := smoothSum_intervalPolynomial hx hy ht.1 (P := P) (fun _ => 1) ω
    dsimp only
    simpa only [one_mul] using congrArg (fun z : ℂ => ‖z‖^2) hs
  simp_rw [show smoothMainIntegral x P y = _ from funext heq]
  exact intervalPolynomial_average_integrable _ _ (fun _ => ‖(1 : ℂ)‖)
    (fun n _ => lowerCoefficient_measurable x (fun _ => 1) n)
    (fun t n _ => lowerCoefficient_norm_le x (fun _ => 1) t n) hyx

theorem smoothInverseIntegral_integrable {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (P : ℝ) :
    Integrable (smoothInverseIntegral x P y) phaseMeasure := by
  have hx : x ≠ 0 := (hy.trans_le hyx).ne'
  have heq (ω : PhaseSpace) : smoothInverseIntegral x P y ω =
      (1/x)*smoothMainIntegral x P y ω := by
    rw [smoothMainIntegral_eq_inverse hy hyx]
    field_simp
  simp_rw [show smoothInverseIntegral x P y = _ from funext heq]
  exact (smoothMainIntegral_integrable hy hyx P).const_mul (1/x)

theorem smoothInverseIntegral_nonneg {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (P : ℝ) (ω : PhaseSpace) : 0 ≤ smoothInverseIntegral x P y ω := by
  have hx : 0 < x := hy.trans_le hyx
  have h := smoothMainIntegral_nonneg hyx P ω
  rw [smoothMainIntegral_eq_inverse hy hyx] at h
  exact nonneg_of_mul_nonneg_right h hx

theorem smoothRoughAverage_one (x P y X : ℝ) (ω : PhaseSpace) :
    smoothRoughAverage x P y X (fun _ => 1) ω =
      ∑ m ∈ roughAverageSupport ⌊x⌋₊ P y,
        smoothAverage x P (m : ℝ) X (fun n => steinhaus n ω) := by
  simp only [smoothRoughAverage, one_mul]

theorem smoothRoughAverage_le_mainIntegral {x P y X C : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hX : 0 < X) (hshort : ∀ t : ℝ, y ≤ t → roughShortWeight t P X ≤ C) (ω : PhaseSpace) :
    smoothRoughAverage x P y X (fun _ => 1) ω ≤ C*smoothMainIntegral x P y ω := by
  rw [smoothRoughAverage_one]
  exact sum_smoothAverage_le hy hyx hX hshort _

theorem smoothRoughAverage_le_inverseIntegral {x P y X C : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hX : 0 < X) (hshort : ∀ t : ℝ, y ≤ t → roughShortWeight t P X ≤ C) (ω : PhaseSpace) :
    smoothRoughAverage x P y X (fun _ => 1) ω ≤ (C*x)*smoothInverseIntegral x P y ω := by
  have h := smoothRoughAverage_le_mainIntegral hy hyx hX hshort ω
  rwa [smoothMainIntegral_eq_inverse hy hyx, ← mul_assoc] at h

end NField.Alignment.HarperMainIntegral
