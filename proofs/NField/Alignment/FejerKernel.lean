/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-! # Positive Fejér kernels on the unit circle

The normalization is the probability Haar measure on `AddCircle 1`.
The finite character expansion, exact Fourier coefficients and quantitative
tail bounds provide the smoothing kernel for weighted interval discrepancy.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.FejerKernel

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-- The one-sided finite character sum. -/
def characterSum (H : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ r ∈ Finset.range H, fourier (r : ℤ) x

/-- The nonnegative Fejér kernel; the zero-order kernel is identically zero. -/
def kernel (H : ℕ) (x : AddCircle (1 : ℝ)) : ℝ :=
  ‖characterSum H x‖ ^ 2 / H

theorem continuous_characterSum (H : ℕ) : Continuous (characterSum H) := by
  unfold characterSum
  fun_prop

theorem continuous_kernel (H : ℕ) : Continuous (kernel H) := by
  exact ((continuous_characterSum H).norm.pow 2).div_const _

theorem integrable_kernel (H : ℕ) : Integrable (kernel H) AddCircle.haarAddCircle := by
  exact integrableOn_univ.mp ((continuous_kernel H).continuousOn.integrableOn_compact
    isCompact_univ)

theorem kernel_nonneg (H : ℕ) (x : AddCircle (1 : ℝ)) : 0 ≤ kernel H x := by
  unfold kernel
  positivity

theorem kernel_zero (H : ℕ) : kernel H 0 = H := by
  by_cases hH : H = 0
  · subst H
    simp [kernel, characterSum]
  simp only [kernel, characterSum, fourier_eval_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  rw [pow_two, mul_div_cancel_right₀ _ (by exact_mod_cast hH : (H : ℝ) ≠ 0)]

/-- The positive kernel is exactly a finite sum of difference characters. -/
theorem kernel_expansion (H : ℕ) (x : AddCircle (1 : ℝ)) :
    (kernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H, fourier ((r : ℤ) - s) x := by
  have he : ((‖characterSum H x‖ ^ 2 : ℝ) : ℂ) =
      characterSum H x * conj (characterSum H x) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  unfold kernel
  rw [Complex.ofReal_div]
  rw [he]
  simp only [characterSum, map_sum, div_eq_inv_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,
    ← fourier_neg, ← fourier_add, ← sub_eq_add_neg, Complex.ofReal_natCast]

private theorem integrable_fourier (k : ℤ) :
    Integrable (fourier k : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle := by
  exact integrableOn_univ.mp ((fourier k).continuous.continuousOn.integrableOn_compact
    isCompact_univ)

/-- Character orthogonality turns each coefficient into an exact pair count. -/
theorem coefficient_pairs (H : ℕ) (k : ℤ) :
    fourierCoeff (fun x => (kernel H x : ℂ)) k = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
        if k = (r : ℤ) - s then (1 : ℂ) else 0 := by
  simp_rw [kernel_expansion]
  rw [fourierCoeff.const_mul]
  congr 1
  rw [show (fun x : AddCircle (1 : ℝ) => ∑ r ∈ Finset.range H,
      ∑ s ∈ Finset.range H, fourier ((r : ℤ) - s) x) =
      ∑ r ∈ Finset.range H,
      ∑ s ∈ Finset.range H, (fourier ((r : ℤ) - s) : AddCircle (1 : ℝ) → ℂ) by
    ext x
    simp only [Finset.sum_apply]]
  rw [fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro r hr
    rw [fourierCoeff.sum]
    · simp [Finset.sum_apply, fourierCoeff_fourier, Pi.single_apply]
    · intro s hs
      exact integrable_fourier _
  · intro r hr
    exact integrable_finsetSum' (Finset.range H)
      (f := fun s => (fourier ((r : ℤ) - s) : AddCircle (1 : ℝ) → ℂ))
      (fun s hs => integrable_fourier _)

private theorem pair_count_nat (H k : ℕ) :
    (∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
      if (k : ℤ) = (r : ℤ) - s then (1 : ℂ) else 0) = (H - k : ℕ) := by
  rw [Finset.sum_comm]
  have he : ∀ r s : ℕ, (k : ℤ) = r - s ↔ r = s + k := by omega
  simp_rw [he, Finset.sum_ite_eq', Finset.mem_range]
  have hf : (Finset.range H).filter (fun s => s + k < H) = Finset.range (H - k) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf]
  simp

/-- The Fourier coefficients have the exact triangular shape, including zero order. -/
theorem coefficient (H : ℕ) (k : ℤ) :
    fourierCoeff (fun x => (kernel H x : ℂ)) k =
      ((H - k.natAbs : ℕ) : ℂ) / H := by
  rw [coefficient_pairs]
  have hp : (∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
      if k = (r : ℤ) - s then (1 : ℂ) else 0) = (H - k.natAbs : ℕ) := by
    cases k with
    | ofNat k => exact pair_count_nat H k
    | negSucc k =>
      rw [Finset.sum_comm]
      have he : ∀ r s : ℕ, Int.negSucc k = (r : ℤ) - s ↔
          ((k + 1 : ℕ) : ℤ) = (s : ℤ) - r := by omega
      simp_rw [he]
      exact pair_count_nat H (k + 1)
  rw [hp]
  ring

/-- All frequencies of magnitude at least the order are absent. -/
theorem coefficient_eq_zero (H : ℕ) (k : ℤ) (hk : H ≤ k.natAbs) :
    fourierCoeff (fun x => (kernel H x : ℂ)) k = 0 := by
  rw [coefficient, Nat.sub_eq_zero_of_le hk]
  simp

/-- The normalized kernel has total mass one at every positive order. -/
theorem integral_kernel (H : ℕ) (hH : 0 < H) :
    ∫ x, kernel H x ∂AddCircle.haarAddCircle = 1 := by
  apply Complex.ofReal_injective
  have he := coefficient H 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at he
  calc
    ((∫ x, kernel H x ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
        ∫ x, (kernel H x : ℂ) ∂AddCircle.haarAddCircle := integral_complex_ofReal.symm
    _ = 1 := by rw [he]; simp [Nat.ne_of_gt hH]
    _ = (↑(1 : ℝ) : ℂ) := by norm_num

theorem kernel_neg (H : ℕ) (x : AddCircle (1 : ℝ)) : kernel H (-x) = kernel H x := by
  have he : ∀ k : ℤ, fourier k (-x) = conj (fourier k x) := by
    intro k
    rw [fourier_apply, smul_neg, ← neg_smul, ← fourier_apply, fourier_neg]
  have hs : characterSum H (-x) = conj (characterSum H x) := by
    simp only [characterSum, he, map_sum]
  simp only [kernel, hs, Complex.norm_conj]

/-- Reflection about the midpoint of a real period preserves the kernel. -/
theorem kernel_one_sub (H : ℕ) (t : ℝ) :
    kernel H ((1 - t : ℝ) : AddCircle (1 : ℝ)) = kernel H (t : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, kernel_neg]

private theorem fourier_nat_pow (r : ℕ) (x : AddCircle (1 : ℝ)) :
    fourier (r : ℤ) x = fourier 1 x ^ r := by
  rw [fourier_apply, Nat.cast_smul_eq_nsmul, AddCircle.toCircle_nsmul,
    Circle.coe_pow, fourier_one]

/-- The geometric-sum identity, valid even at the integer singularity. -/
theorem characterSum_mul (H : ℕ) (x : AddCircle (1 : ℝ)) :
    characterSum H x * (fourier 1 x - 1) = fourier (H : ℤ) x - 1 := by
  simp only [characterSum, fourier_nat_pow]
  exact geom_sum_mul _ _

/-- The denominator in the geometric-sum formula is twice the sine distance. -/
theorem character_distance (t : ℝ) :
    ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [fourier_coe_apply]
  have he : (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (t : ℂ) / (1 : ℝ)) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  norm_num [Real.norm_eq_abs, abs_mul]
  congr 2
  ring

/-- Away from zero, the kernel is bounded by an explicit inverse square. -/
theorem kernel_le_inverse_square (H : ℕ) (hH : 0 < H) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    kernel H (t : AddCircle (1 : ℝ)) ≤ 1 / (4 * (H : ℝ) * t ^ 2) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hs := Real.mul_le_sin (x := Real.pi * t)
    (by positivity) (by nlinarith [Real.pi_pos])
  have hs' : 2 * t ≤ Real.sin (Real.pi * t) := by
    calc
      2 * t = 2 / Real.pi * (Real.pi * t) := by field_simp
      _ ≤ _ := hs
  have hd : 4 * t ≤ ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ := by
    rw [character_distance]
    nlinarith [le_abs_self (Real.sin (Real.pi * t))]
  have he := congrArg norm (characterSum_mul H (t : AddCircle (1 : ℝ)))
  rw [norm_mul] at he
  have hn : ‖fourier (H : ℤ) (t : AddCircle (1 : ℝ)) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier (H : ℤ) (t : AddCircle (1 : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [fourier_apply, Circle.norm_coe, norm_one]; norm_num
  have hp : ‖characterSum H (t : AddCircle (1 : ℝ))‖ * (2 * t) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hd (norm_nonneg (characterSum H (t : AddCircle (1 : ℝ))))
    nlinarith
  have hp0 : 0 ≤ ‖characterSum H (t : AddCircle (1 : ℝ))‖ * (2 * t) := by positivity
  have hp2 := pow_le_pow_left₀ hp0 hp 2
  unfold kernel
  apply (le_div_iff₀ (by positivity : 0 < 4 * (H : ℝ) * t ^ 2)).mpr
  calc
    _ = ‖characterSum H (t : AddCircle (1 : ℝ))‖ ^ 2 * (4 * t ^ 2) := by
      field_simp
    _ ≤ 1 := by nlinarith

theorem continuous_real_kernel (H : ℕ) :
    Continuous (fun t : ℝ => kernel H (t : AddCircle (1 : ℝ))) :=
  (continuous_kernel H).comp (AddCircle.continuous_mk' 1)

/-- A real period has the same unit mass as the probability Haar integral. -/
theorem integral_real_kernel (H : ℕ) (hH : 0 < H) (a : ℝ) :
    ∫ t in a..a + 1, kernel H (t : AddCircle (1 : ℝ)) = 1 := by
  have he := AddCircle.intervalIntegral_preimage (1 : ℝ) a (kernel H)
  simpa [AddCircle.volume_eq_smul_haarAddCircle, integral_kernel H hH] using he

/-- Integrating the inverse-square majorant controls one side of the tail. -/
theorem half_tail_bound (H : ℕ) (hH : 0 < H) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∫ t in δ..(1 / 2 : ℝ), kernel H (t : AddCircle (1 : ℝ)) ≤
      1 / (4 * (H : ℝ) * δ) := by
  have h0 : (0 : ℝ) ∉ uIcc δ (1 / 2) := by
    rw [uIcc_of_le hδ']
    simp only [mem_Icc, not_and_or]
    exact Or.inl (by linarith)
  have hform (t : ℝ) : 1 / (4 * (H : ℝ) * t ^ 2) =
      (4 * (H : ℝ))⁻¹ * t ^ (-2 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat, one_div, mul_inv_rev]
    ring
  have hi := (intervalIntegral.intervalIntegrable_zpow (n := (-2 : ℤ)) (μ := volume)
    (Or.inr h0)).const_mul
    ((4 * (H : ℝ))⁻¹)
  have hm := intervalIntegral.integral_mono_on hδ'
    ((continuous_real_kernel H).intervalIntegrable δ (1 / 2)) hi
    (fun t ht => (kernel_le_inverse_square H hH t (lt_of_lt_of_le hδ ht.1) ht.2).trans_eq
      (hform t))
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)] at hm
  norm_num at hm
  calc
    _ ≤ (4 * (H : ℝ))⁻¹ * (δ⁻¹ - 2) := hm.trans_eq (by simp only [mul_inv_rev]; ring)
    _ ≤ (4 * (H : ℝ))⁻¹ * δ⁻¹ :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1 / (4 * (H : ℝ) * δ) := by simp only [mul_inv_rev, one_div]; ring

/-- The total mass outside distance `δ` from the integers is at most `1/(2Hδ)`.
The endpoints are retained; no property of a finite sample is asserted almost everywhere. -/
theorem tail_bound (H : ℕ) (hH : 0 < H) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∫ t in δ..(1 - δ), kernel H (t : AddCircle (1 : ℝ)) ≤
      1 / (2 * (H : ℝ) * δ) := by
  have hs : (∫ t in (1 / 2 : ℝ)..(1 - δ), kernel H (t : AddCircle (1 : ℝ))) =
      ∫ t in δ..(1 / 2 : ℝ), kernel H (t : AddCircle (1 : ℝ)) := by
    calc
      _ = ∫ t in (1 / 2 : ℝ)..(1 - δ), kernel H ((1 - t : ℝ) : AddCircle (1 : ℝ)) := by
        simp_rw [kernel_one_sub]
      _ = ∫ t in (1 - (1 - δ))..(1 - 1 / 2 : ℝ), kernel H (t : AddCircle (1 : ℝ)) :=
        intervalIntegral.integral_comp_sub_left
          (fun t : ℝ => kernel H (t : AddCircle (1 : ℝ))) (1 : ℝ)
      _ = _ := by norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_real_kernel H).intervalIntegrable δ (1 / 2))
    ((continuous_real_kernel H).intervalIntegrable (1 / 2) (1 - δ)), hs]
  calc
    _ ≤ 2 * (1 / (4 * (H : ℝ) * δ)) := by linarith [half_tail_bound H hH δ hδ hδ']
    _ = 1 / (2 * (H : ℝ) * δ) := by ring

/-- The complementary neighborhood of the integers retains almost all the mass. -/
theorem central_mass_lower_bound (H : ℕ) (hH : 0 < H) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    1 - 1 / (2 * (H : ℝ) * δ) ≤
      ∫ t in (-δ)..δ, kernel H (t : AddCircle (1 : ℝ)) := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((continuous_real_kernel H).intervalIntegrable (μ := volume) (-δ) δ)
    ((continuous_real_kernel H).intervalIntegrable δ (1 - δ))
  have hm : (∫ t in (-δ)..(1 - δ), kernel H (t : AddCircle (1 : ℝ))) = 1 := by
    simpa only [sub_eq_add_neg, add_comm] using integral_real_kernel H hH (-δ)
  rw [hm] at hs
  linarith [tail_bound H hH δ hδ hδ']

/-- At radius `1/sqrt(H)` the tail is at most `1/(2sqrt(H))`. -/
theorem tail_bound_sqrt (H : ℕ) (hH : 16 ≤ H) :
    ∫ t in (Real.sqrt (H : ℝ))⁻¹..(1 - (Real.sqrt (H : ℝ))⁻¹),
      kernel H (t : AddCircle (1 : ℝ)) ≤ 1 / (2 * Real.sqrt (H : ℝ)) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hs0 := Real.sqrt_pos.mpr hH0
  have hs4 : 4 ≤ Real.sqrt (H : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hH0.le).mpr
    exact_mod_cast hH
  have hδ : (Real.sqrt (H : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [← one_div, div_le_iff₀ hs0]
    nlinarith
  have ht := tail_bound H (by omega) _ (by positivity) hδ
  have he : (H : ℝ) * (Real.sqrt (H : ℝ))⁻¹ = Real.sqrt (H : ℝ) := by
    rw [← div_eq_mul_inv]
    exact (div_eq_iff hs0.ne').mpr (by nlinarith [Real.sq_sqrt hH0.le])
  simpa only [mul_assoc, he] using ht

end NField.Alignment.FejerKernel
