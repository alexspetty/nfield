/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerIntervalSmoothing

/-! # Fourier representation of the smoothed interval
The interval may extend beyond a single period. Both endpoints are retained.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FejerWindowFourier
open MeasureTheory Set FejerKernel FejerIntervalSmoothing
open scoped BigOperators

def arcCoefficient (a b : ℝ) (k : ℤ) : ℂ :=
  ∫ t in a..b, fourier (-k) (t : AddCircle (1 : ℝ))

theorem continuous_character (k : ℤ) :
    Continuous (fun t : ℝ => fourier k (t : AddCircle (1 : ℝ))) :=
  (fourier k).continuous.comp (AddCircle.continuous_mk' 1)

theorem arcCoefficient_zero (a b : ℝ) : arcCoefficient a b 0 = (b - a : ℝ) := by
  simp [arcCoefficient]

theorem character_sub (k : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier k (x-y) = fourier k x * fourier (-k) y := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, neg_smul,
    AddCircle.toCircle_add, Circle.coe_mul]

theorem arcCoefficient_formula (a b : ℝ) (k : ℤ) (hk : k ≠ 0) :
    arcCoefficient a b k =
      (fourier (-k) (b : AddCircle (1 : ℝ)) - fourier (-k) (a : AddCircle (1 : ℝ))) /
        (2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ)) := by
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (by exact_mod_cast neg_ne_zero.mpr hk)
  unfold arcCoefficient
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  exact integral_exp_mul_complex hc

theorem arcCoefficient_norm (a b : ℝ) (k : ℤ) (hk : k ≠ 0) :
    ‖arcCoefficient a b k‖ ≤ 1 / (Real.pi * |(k : ℝ)|) := by
  rw [arcCoefficient_formula a b k hk, norm_div]
  have hn : ‖fourier (-k) (b : AddCircle (1 : ℝ)) -
      fourier (-k) (a : AddCircle (1 : ℝ))‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier (-k) (b : AddCircle (1 : ℝ))‖ +
          ‖fourier (-k) (a : AddCircle (1 : ℝ))‖ := norm_sub_le _ _
      _ = 2 := by simp only [fourier_apply, Circle.norm_coe]; norm_num
  have hd : ‖2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ)‖ =
      2 * Real.pi * |(k : ℝ)| := by
    simp [Complex.norm_intCast, abs_of_pos Real.pi_pos]
  rw [hd]
  calc
    _ ≤ 2 / (2 * Real.pi * |(k : ℝ)|) := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by ring

/-- Exact finite Fourier representation of the actual interval window. -/
theorem window_expansion (H : ℕ) (a b : ℝ) (x : AddCircle (1 : ℝ)) :
    (window H a b x : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
        fourier ((r : ℤ) - s) x * arcCoefficient a b ((r : ℤ) - s) := by
  unfold window
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [kernel_expansion, character_sub]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      exact intervalIntegral.integral_const_mul _ _
    · intro s hs
      exact (continuous_const.mul (continuous_character _)).intervalIntegrable a b
  · intro r hr
    apply Continuous.intervalIntegrable
    fun_prop

/-- The window is continuous, as its character polynomial is finite. -/
theorem continuous_window_complex (H : ℕ) (a b : ℝ) :
    Continuous (fun x => (window H a b x : ℂ)) := by
  simp_rw [window_expansion]
  fun_prop

/-- Each window coefficient is the kernel coefficient times the interval integral. -/
theorem window_coefficient (H : ℕ) (a b : ℝ) (k : ℤ) :
    fourierCoeff (fun x => (window H a b x : ℂ)) k =
      fourierCoeff (fun x => (kernel H x : ℂ)) k * arcCoefficient a b k := by
  have hi (n : ℤ) : Integrable
      (fun x : AddCircle (1 : ℝ) => fourier n x * arcCoefficient a b n)
      AddCircle.haarAddCircle := by
    exact integrableOn_univ.mp
      (((fourier n).continuous.mul continuous_const).continuousOn.integrableOn_compact isCompact_univ)
  have ht (n : ℤ) : fourierCoeff
      (fun x : AddCircle (1 : ℝ) => fourier n x * arcCoefficient a b n) k =
      (if k = n then (1 : ℂ) else 0) * arcCoefficient a b k := by
    rw [show (fun x : AddCircle (1 : ℝ) => fourier n x * arcCoefficient a b n) =
      (fun x => arcCoefficient a b n * fourier n x) by ext x; ring]
    rw [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply]
    split_ifs with h
    · subst n; simp
    · simp
  simp_rw [window_expansion]
  rw [fourierCoeff.const_mul]
  rw [show (fun x : AddCircle (1 : ℝ) => ∑ r ∈ Finset.range H,
      ∑ s ∈ Finset.range H, fourier ((r : ℤ)-s) x * arcCoefficient a b ((r : ℤ)-s)) =
      ∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
        (fun x : AddCircle (1 : ℝ) => fourier ((r : ℤ)-s) x * arcCoefficient a b ((r : ℤ)-s)) by
    ext x; simp only [Finset.sum_apply]]
  rw [fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    have hs (r : ℕ) : fourierCoeff (∑ s ∈ Finset.range H,
        (fun x : AddCircle (1 : ℝ) => fourier ((r : ℤ)-s) x * arcCoefficient a b ((r : ℤ)-s))) k =
        ∑ s ∈ Finset.range H, (if k = (r : ℤ)-s then (1 : ℂ) else 0) * arcCoefficient a b k := by
      rw [fourierCoeff.sum (Finset.range H) _ (fun s _ => hi _)]
      simp only [Finset.sum_apply, ht]
    simp_rw [hs]
    rw [coefficient_pairs]
    simp only [← Finset.sum_mul]
    ring
  · intro r hr
    exact integrable_finsetSum' (Finset.range H) (fun s _ => hi _)

/-- The window mean is exactly the length of the unwrapped interval. -/
theorem window_mean (H : ℕ) (hH : 0 < H) (a b : ℝ) :
    ∫ x, window H a b x ∂AddCircle.haarAddCircle = b-a := by
  have he := window_coefficient H a b 0
  rw [coefficient, arcCoefficient_zero] at he
  simp only [Int.natAbs_zero, Nat.sub_zero, fourierCoeff, neg_zero,
    fourier_zero, one_smul] at he
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hH
  rw [div_self hH0, one_mul] at he
  apply Complex.ofReal_injective
  calc
    ((∫ x, window H a b x ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
        ∫ x, (window H a b x : ℂ) ∂AddCircle.haarAddCircle := integral_complex_ofReal.symm
    _ = ((b-a : ℝ) : ℂ) := he

/-- Smoothing introduces no frequencies of magnitude at least H. -/
theorem window_coefficient_zero (H : ℕ) (a b : ℝ) (k : ℤ) (hk : H ≤ k.natAbs) :
    fourierCoeff (fun x => (window H a b x : ℂ)) k = 0 := by
  rw [window_coefficient, coefficient_eq_zero H k hk, zero_mul]

/-- Nonzero window coefficients retain the uniform inverse-frequency bound. -/
theorem window_coefficient_norm (H : ℕ) (a b : ℝ) (k : ℤ) (hk : k ≠ 0) :
    ‖fourierCoeff (fun x => (window H a b x : ℂ)) k‖ ≤
      1 / (Real.pi * |(k : ℝ)|) := by
  have hc : ‖fourierCoeff (fun x => (kernel H x : ℂ)) k‖ ≤ 1 := by
    rw [coefficient, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    by_cases hH : H = 0
    · subst H; simp
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hH : (0 : ℝ) < H)).mpr
      exact_mod_cast Nat.sub_le H k.natAbs
  rw [window_coefficient, norm_mul]
  calc
    _ ≤ 1 * ‖arcCoefficient a b k‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using arcCoefficient_norm a b k hk

end NField.Alignment.FejerWindowFourier
