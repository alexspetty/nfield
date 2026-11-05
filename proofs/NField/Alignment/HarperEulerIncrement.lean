/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerSecondMoment
import NField.Alignment.HarperShiftedEulerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Mean-square increments of the actual random Euler product

Finite Steinhaus orthogonality and dominated convergence identify the
increment second moment with its exact infinite smooth-coefficient energy,
uniformly in the center frequency. An elementary exponential bound controls
logarithmic weights by the shifted Euler product. The existing logarithmic
bound for that product gives O(t^2 log(P)^3), hence O(log(P)^(49/50)) on
cells of radius 1/(2 log(P)^(101/100)). No increment estimate is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperEulerIncrement
open scoped BigOperators Topology
open MeasureTheory Filter SteinhausMoment HarperSmoothDivisor HarperSmoothCount
  HarperRandomEulerProduct HarperEulerIntegral HarperEulerSecondMoment

def twist (n : ℕ) (t : ℝ) : ℂ := (n : ℂ)^(-(t : ℂ)*Complex.I)
def incrementCoeff (n : ℕ) (t : ℝ) : ℝ := ‖twist n t-1‖^2/(n : ℝ)
def incrementEnergy (P u t : ℝ) (ω : PhaseSpace) : ℝ :=
  ‖eulerProduct P (linePoint (1/2) (u+t)) ω-eulerProduct P (linePoint (1/2) u) ω‖^2

theorem twist_norm {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖twist n t‖ = 1 := by
  unfold twist
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem twist_sub_one_bound {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖twist n t-1‖ ≤ 2 := by
  calc
    _ ≤ ‖twist n t‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by rw [twist_norm hn]; norm_num

theorem incrementCoeff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ incrementCoeff n t := by
  unfold incrementCoeff
  positivity

theorem incrementCoeff_bound {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    incrementCoeff n t ≤ 4/(n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith [twist_sub_one_bound hn t, norm_nonneg (twist n t-1)]

theorem coefficient_difference_norm {n : ℕ} (hn : n ≠ 0) (u t : ℝ) :
    ‖(n : ℂ)^(-linePoint (1/2) (u+t))-(n : ℂ)^(-linePoint (1/2) u)‖^2 =
      incrementCoeff n t := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have he : -linePoint (1/2) (u+t) = -linePoint (1/2) u+(-(t : ℂ)*Complex.I) := by
    simp only [linePoint, Complex.ofReal_add]
    ring
  rw [he, Complex.cpow_add _ _ hnC]
  have hf : (n : ℂ)^(-linePoint (1/2) u)*(n : ℂ)^(-(t : ℂ)*Complex.I)-
      (n : ℂ)^(-linePoint (1/2) u) =
      (n : ℂ)^(-linePoint (1/2) u)*(twist n t-1) := by unfold twist; ring
  rw [hf, norm_mul, mul_pow, cpow_norm_sq hn, linePoint_re]
  norm_num [incrementCoeff, Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

theorem incrementCoeff_summable (P t : ℝ) :
    Summable (fun n : smoothIntegers P => incrementCoeff n t) := by
  apply Summable.of_nonneg_of_le (fun n => incrementCoeff_nonneg n t)
    (f := fun n : smoothIntegers P => 4*((n : ℕ) : ℝ)^(-(1 : ℝ)))
  · intro n
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      incrementCoeff_bound (smoothIntegers_mem.mp n.property).1 t
  · exact (smooth_power_hasSum P (by norm_num : (0 : ℝ) < 1)).summable.mul_left 4

theorem partialIncrement_second_moment (P u t : ℝ) (N : ℕ) :
    (∫ ω, ‖partialEuler P (linePoint (1/2) (u+t)) N ω-
      partialEuler P (linePoint (1/2) u) N ω‖^2 ∂phaseMeasure) =
      ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), incrementCoeff n t := by
  let s := (Finset.range N).filter (· ∈ smoothIntegers P)
  have hn : ∀ n ∈ s, n ≠ 0 := fun n h => (smoothIntegers_mem.mp (Finset.mem_filter.mp h).2).1
  have he (ω : PhaseSpace) : partialEuler P (linePoint (1/2) (u+t)) N ω-
      partialEuler P (linePoint (1/2) u) N ω =
      ∑ n ∈ s, ((n : ℂ)^(-linePoint (1/2) (u+t))-
        (n : ℂ)^(-linePoint (1/2) u))*steinhaus n ω := by
    unfold partialEuler
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Complex.cpow_neg, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [polynomial_second_moment s _ hn]
  exact Finset.sum_congr rfl (fun n hn' => coefficient_difference_norm (hn n hn') u t)

theorem partialIncrement_norm_bound (P u t : ℝ) (N : ℕ) (ω : PhaseSpace) :
    ‖partialEuler P (linePoint (1/2) (u+t)) N ω-partialEuler P (linePoint (1/2) u) N ω‖ ≤
      2*shiftedProduct P (1/2) := by
  have h₁ := partialEuler_norm_bound P (s := linePoint (1/2) (u+t)) (by norm_num [linePoint_re]) N ω
  have h₂ := partialEuler_norm_bound P (s := linePoint (1/2) u) (by norm_num [linePoint_re]) N ω
  simp only [linePoint_re] at h₁ h₂
  exact (norm_sub_le _ _).trans (by linarith)

theorem increment_second_moment (P u t : ℝ) :
    (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) =
      ∑' n : smoothIntegers P, incrementCoeff n t := by
  have hs := (incrementCoeff_summable P t).hasSum
  have hsi : HasSum ((smoothIntegers P).indicator (fun n => incrementCoeff n t))
      (∑' n : smoothIntegers P, incrementCoeff n t) := hasSum_subtype_iff_indicator.mp hs
  have henergy : Tendsto (fun N => ∫ ω, ‖partialEuler P (linePoint (1/2) (u+t)) N ω-
      partialEuler P (linePoint (1/2) u) N ω‖^2 ∂phaseMeasure) atTop
      (𝓝 (∑' n : smoothIntegers P, incrementCoeff n t)) := by
    simpa only [partialIncrement_second_moment, Set.indicator_apply, ← Finset.sum_filter]
      using hsi.tendsto_sum_nat
  have hlim : Tendsto (fun N => ∫ ω, ‖partialEuler P (linePoint (1/2) (u+t)) N ω-
      partialEuler P (linePoint (1/2) u) N ω‖^2 ∂phaseMeasure) atTop
      (𝓝 (∫ ω, incrementEnergy P u t ω ∂phaseMeasure)) := by
    apply tendsto_integral_filter_of_norm_le_const
      (Filter.Eventually.of_forall (fun N => (((partialEuler_measurable P _ N).sub
        (partialEuler_measurable P _ N)).norm.pow_const 2).aestronglyMeasurable))
    · refine ⟨(2*shiftedProduct P (1/2))^2, Filter.Eventually.of_forall (fun N => ?_)⟩
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (partialIncrement_norm_bound P u t N ω) 2
    · exact Filter.Eventually.of_forall (fun ω =>
        (((partialEuler_tendsto P (s := linePoint (1/2) (u+t)) (by norm_num [linePoint_re]) ω).sub
          (partialEuler_tendsto P (s := linePoint (1/2) u) (by norm_num [linePoint_re]) ω)).norm).pow 2)
  exact tendsto_nhds_unique hlim henergy


theorem twist_sub_one_log_bound {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ‖twist n t-1‖ ≤ |t| *Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
  unfold twist
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  have he : (Real.log (n : ℝ) : ℂ)*(-(t : ℂ)*Complex.I) =
      Complex.I*((-(t*Real.log n) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  calc
    _ ≤ ‖-(t*Real.log n)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hn1)]

theorem log_square_bound {n : ℕ} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L) :
    (Real.log n)^2 ≤ 2*L^2*(n : ℝ)^(1/L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Real.pow_div_factorial_le_exp (Real.log n/L)
    (div_nonneg (Real.log_nonneg hn1) hL.le) 2
  have he : Real.exp (Real.log n/L) = (n : ℝ)^(1/L) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  rw [he] at h
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  have hh : (Real.log n)^2/L^2 ≤ 2*(n : ℝ)^(1/L) := by
    rw [← div_pow]
    linarith
  have hhh := (div_le_iff₀ (sq_pos_of_pos hL)).mp hh
  nlinarith

theorem incrementCoeff_shifted_bound {P : ℝ} (hP : 0 < Real.log P)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    incrementCoeff n t ≤ (2*t^2*(Real.log P)^2)*(n : ℝ)^(-HarperShiftedEulerProduct.shift P) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have htw := pow_le_pow_left₀ (norm_nonneg _) (twist_sub_one_log_bound hn t) 2
  have hl := log_square_bound hn hP
  have hr : (n : ℝ)^(1/Real.log P)/(n : ℝ) = (n : ℝ)^(-HarperShiftedEulerProduct.shift P) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hnR]
    congr 1
    unfold HarperShiftedEulerProduct.shift
    ring
  calc
    _ ≤ (|t| *Real.log n)^2/(n : ℝ) := div_le_div_of_nonneg_right htw hnR.le
    _ = t^2*(Real.log n)^2/(n : ℝ) := by rw [mul_pow, sq_abs]
    _ ≤ (t^2*(2*(Real.log P)^2*(n : ℝ)^(1/Real.log P)))/(n : ℝ) := by gcongr
    _ = (2*t^2*(Real.log P)^2)*((n : ℝ)^(1/Real.log P)/(n : ℝ)) := by ring
    _ = _ := by rw [hr]

theorem increment_second_moment_bound {P : ℝ} (hP : 2 ≤ Real.log P) (u t : ℝ) :
    (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) ≤
      (2*t^2*(Real.log P)^2)*shiftedProduct P (HarperShiftedEulerProduct.shift P) := by
  have hs : 0 < HarperShiftedEulerProduct.shift P := by
    linarith [(HarperShiftedEulerProduct.shift_bounds hP).1]
  rw [increment_second_moment]
  calc
    _ ≤ ∑' n : smoothIntegers P,
        (2*t^2*(Real.log P)^2)*((n : ℕ) : ℝ)^(-HarperShiftedEulerProduct.shift P) :=
      (incrementCoeff_summable P t).tsum_le_tsum
        (fun n => incrementCoeff_shifted_bound (by linarith) (smoothIntegers_mem.mp n.property).1 t)
        ((smooth_power_hasSum P hs).summable.mul_left _)
    _ = _ := by rw [tsum_mul_left, (smooth_power_hasSum P hs).tsum_eq]

theorem eventual_increment_second_moment_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ u t : ℝ, (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) ≤ C*t^2*(Real.log P)^3 := by
  obtain ⟨C,hC,hb⟩ := HarperShiftedEulerProduct.eventual_shiftedProduct_log_bound
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 2] with P hbound hP
  intro u t
  calc
    _ ≤ (2*t^2*(Real.log P)^2)*shiftedProduct P (HarperShiftedEulerProduct.shift P) :=
      increment_second_moment_bound hP u t
    _ ≤ (2*t^2*(Real.log P)^2)*(C*Real.log P) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem small_increment_power_bound {L t : ℝ} (hL : 0 < L)
    (ht : |t| ≤ 1/(2*L^(101/100 : ℝ))) : t^2*L^3 ≤ L^(49/50 : ℝ) := by
  have ht' : |t| ≤ L^(-(101/100 : ℝ)) := by
    rw [Real.rpow_neg hL.le]
    exact ht.trans (by
      rw [inv_eq_one_div]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _)
      nlinarith [Real.rpow_pos_of_pos hL (101/100 : ℝ)])
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht' 2
  rw [sq_abs] at ht2
  calc
    _ ≤ (L^(-(101/100 : ℝ)))^2*L^3 := mul_le_mul_of_nonneg_right ht2 (by positivity)
    _ = L^((-(101/100 : ℝ))*2+3) := by
      rw [← Real.rpow_mul_natCast hL.le, ← Real.rpow_natCast L 3, ← Real.rpow_add hL]
      norm_num
    _ = _ := by norm_num

theorem eventual_small_increment_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ u t : ℝ, |t| ≤ 1/(2*(Real.log P)^(101/100 : ℝ)) →
      (∫ ω, incrementEnergy P u t ω ∂phaseMeasure) ≤ C*(Real.log P)^(49/50 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_increment_second_moment_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_gt_atTop 0] with P hbound hP
  intro u t ht
  calc
    _ ≤ C*t^2*(Real.log P)^3 := hbound u t
    _ = C*(t^2*(Real.log P)^3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (small_increment_power_bound hP ht) hC.le

end NField.Alignment.HarperEulerIncrement
