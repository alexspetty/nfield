/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartitionFourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact derivative constant for the constructed Harper cell

The bound is obtained by integrating the polynomial frequency weight over
the actual compact band. No derivative estimate is assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set FourierTransform

namespace NField.Alignment.HarperPartitionDerivative

open HarperPartition HarperPartitionFourier

def derivativeBound (delta : ℝ) (n : ℕ) : ℝ :=
  (2*Real.pi/delta)^(n+1) / (Real.pi*((n : ℝ)+1))

theorem integral_abs_pow_band {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (∫ t in Icc (-r) r, |t|^n) = 2*r^(n+1)/((n : ℝ)+1) := by
  have hc : Continuous (fun t : ℝ => |t|^n) := continuous_abs.pow n
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hl : (∫ t in (-r)..0, |t|^n) = ∫ t in 0..r, |t|^n := by
    have h := intervalIntegral.integral_comp_neg (fun t : ℝ => |t|^n) (a := -r) (b := 0)
    simpa only [abs_neg, neg_zero, neg_neg] using h
  have hh : (∫ t in 0..r, |t|^n) = r^(n+1)/((n : ℝ)+1) := by
    calc
      _ = ∫ t in 0..r, t^n := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr] at ht
        change |t|^n = t^n
        rw [abs_of_nonneg ht.1]
      _ = _ := by rw [integral_pow]; simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-r) 0)
    (hc.intervalIntegrable 0 r), hl, hh]
  ring

theorem density_moment_bound {delta : ℝ} (hd : 0 < delta) (n : ℕ) :
    (∫ t : ℝ, |t|^n * ‖density delta t‖) ≤ 2*(delta⁻¹)^(n+1)/((n : ℝ)+1) := by
  have hf : Integrable (fun t : ℝ => |t|^n * ‖density delta t‖) := by
    simpa only [norm_smul, norm_pow, Real.norm_eq_abs] using (integrable_density_moment hd n).norm
  have hg : Integrable ((Icc (-delta⁻¹) delta⁻¹).indicator (fun t : ℝ => |t|^n)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (continuous_abs.pow n : Continuous (fun t : ℝ => |t|^n)).integrableOn_Icc
  have h := integral_mono hf hg (fun t => ?_)
  · rw [integral_indicator measurableSet_Icc, integral_abs_pow_band (inv_nonneg.mpr hd.le)] at h
    exact h
  · by_cases ht : t ∈ Icc (-delta⁻¹) delta⁻¹
    · rw [indicator_of_mem ht]
      exact (mul_le_mul_of_nonneg_left (density_norm_le_one delta t) (by positivity)).trans_eq
        (mul_one _)
    · rw [indicator_of_notMem ht]
      have hz : density delta t = 0 := by
        apply density_zero_of_outside hd
        by_contra h
        exact ht (abs_le.mp (le_of_lt (lt_of_not_ge h)))
      simp [hz]

theorem cell_derivative_bound {delta : ℝ} (hd : 0 < delta) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (cell delta) x| ≤ derivativeBound delta n := by
  rw [← cell_iteratedDeriv_norm hd, cell_iteratedDeriv_fourier hd, Real.fourier_eq]
  have he (t : ℝ) : ‖(-2*Real.pi*Complex.I*t)^n • density delta t‖ =
      (2*Real.pi)^n * (|t|^n * ‖density delta t‖) := by
    simp only [norm_smul, norm_pow, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_pow]
    norm_num
    ring
  calc
    _ ≤ ∫ t : ℝ, (2*Real.pi)^n * (|t|^n * ‖density delta t‖) := by
      convert norm_integral_le_integral_norm
        (fun t : ℝ => Real.fourierChar (-inner ℝ t x) •
          ((-2*Real.pi*Complex.I*t)^n • density delta t)) using 1
      simp only [Circle.norm_smul, he]
    _ = (2*Real.pi)^n * ∫ t : ℝ, |t|^n * ‖density delta t‖ := integral_const_mul _ _
    _ ≤ (2*Real.pi)^n * (2*(delta⁻¹)^(n+1)/((n : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (density_moment_bound hd n) (by positivity)
    _ = derivativeBound delta n := by
      unfold derivativeBound
      rw [div_pow, pow_succ (2*Real.pi), inv_pow]
      field_simp [hd.ne', Real.pi_ne_zero]

theorem derivativeBound_nonneg {delta : ℝ} (hd : 0 < delta) (n : ℕ) :
    0 ≤ derivativeBound delta n := by unfold derivativeBound; positivity

theorem contDiff_cellSum {delta : ℝ} (hd : 0 < delta) (J : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cellSum delta J) := by
  unfold cellSum
  exact ContDiff.sum fun i _ => (contDiff_cell hd).comp
    ((contDiff_id.add contDiff_const).sub contDiff_const)

theorem contDiff_outside {delta : ℝ} (hd : 0 < delta) (J : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (outside delta J) :=
  contDiff_const.sub (contDiff_cellSum hd J)

theorem contDiff_labelWeight {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) : ContDiff ℝ (⊤ : ℕ∞) (labelWeight delta J i) := by
  unfold labelWeight
  split_ifs
  · exact (contDiff_cell hd).comp ((contDiff_id.add contDiff_const).sub contDiff_const)
  · exact contDiff_outside hd J

theorem cellSum_derivative_bound {delta : ℝ} (hd : 0 < delta) (J n : ℕ) (x : ℝ) :
    |iteratedDeriv n (cellSum delta J) x| ≤ (2*J+1 : ℝ)*derivativeBound delta n := by
  have hf (i : ℕ) : ContDiff ℝ n (fun x : ℝ => cell delta (x+i-J)) :=
    (contDiff_cell hd).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) |>.comp
      ((contDiff_id.add contDiff_const).sub contDiff_const)
  unfold cellSum
  rw [iteratedDeriv_fun_sum (fun i _ => (hf i).contDiffAt)]
  simp_rw [add_sub_assoc, iteratedDeriv_comp_add_const]
  calc
    _ ≤ ∑ i ∈ Finset.range (2*J+1), |iteratedDeriv n (cell delta) (x+(i-J))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2*J+1), derivativeBound delta n :=
      Finset.sum_le_sum fun i _ => cell_derivative_bound hd n (x+(i-J))
    _ = _ := by simp

theorem outside_derivative_bound {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |iteratedDeriv n (outside delta J) x| ≤ (2*J+1 : ℝ)*derivativeBound delta n := by
  unfold outside
  rw [iteratedDeriv_const_sub hn, iteratedDeriv_neg, abs_neg]
  exact cellSum_derivative_bound hd J n x

theorem labelWeight_derivative_bound {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |iteratedDeriv n (labelWeight delta J i) x| ≤
      (2*J+1 : ℝ)*derivativeBound delta n := by
  unfold labelWeight
  split_ifs
  · simp only [add_sub_assoc, iteratedDeriv_comp_add_const]
    exact (cell_derivative_bound hd n _).trans
      (le_mul_of_one_le_left (derivativeBound_nonneg hd n)
        (by nlinarith [Nat.cast_nonneg (α := ℝ) J]))
  · exact outside_derivative_bound hd J hn x

theorem labelWeight_le_one {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) (x : ℝ) : labelWeight delta J i x ≤ 1 := by
  rw [← labelWeight_sum delta J x]
  exact Finset.single_le_sum (fun j _ => labelWeight_nonneg hd J j x) (Finset.mem_univ i)

end NField.Alignment.HarperPartitionDerivative
