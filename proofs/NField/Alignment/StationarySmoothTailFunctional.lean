/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryReciprocalFloorIntegral

/-! # The matching exact tail functional for a smooth cumulative weight -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationarySmoothTailFunctional
open scoped BigOperators
open MeasureTheory Set StationaryDiagonalDefinitions StationaryFloorInterchange
  StationarySawtoothIntegrals StationaryTailFunctional StationaryReciprocalFloorIntegral

theorem derivative_reciprocal_integral {F F' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t) (hc : ContinuousOn F' (Icc a b)) :
    (∫ t in a..b, F' t / t) = F b / b - F a / a + ∫ t in a..b, F t / t ^ 2 := by
  have hne : ∀ {t : ℝ}, t ∈ uIcc a b → t ≠ 0 :=
    fun ht => positive_interval_ne_zero ha hab ht
  have hcInv : ContinuousOn (fun t : ℝ => -1 / t ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (hne ht))
  have hc' : ContinuousOn F' (uIcc a b) := by rwa [uIcc_of_le hab]
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => inverse_hasDerivAt (hne ht))
    (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht))
    hcInv.intervalIntegrable hc'.intervalIntegrable
  have hl (t : ℝ) : (1 / t) * F' t = F' t / t := by ring
  have hr (t : ℝ) : (-1 / t ^ 2) * F t = -(F t / t ^ 2) := by ring
  simp only [hl, hr, intervalIntegral.integral_neg] at hh
  convert! hh using 1
  ring

/-- Title: `The smooth sawtooth integral equals the same exact tail functional`. -/
theorem smooth_psi_tail_functional {F F' : ℝ → ℝ} {M n : ℕ}
    (hM : 0 < M) (hMn : M ≤ n)
    (hd : ∀ t ∈ Icc (M : ℝ) n, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Icc (M : ℝ) n)) :
    (∫ t in (M : ℝ)..n, F' t * psi ((n : ℝ) / t)) = tailFunctional F M n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (hMR.trans_le hMnR)
  have hne : ∀ {t : ℝ}, t ∈ uIcc (M : ℝ) n → t ≠ 0 :=
    fun ht => positive_interval_ne_zero hMR hMnR ht
  have hc' : ContinuousOn F' (uIcc (M : ℝ) n) := by rwa [uIcc_of_le hMnR]
  have hi : IntervalIntegrable F' volume (M : ℝ) n := hc'.intervalIntegrable
  have hci : ContinuousOn (fun t : ℝ => 1 / t) (uIcc (M : ℝ) n) :=
    continuousOn_const.div continuousOn_id (fun t ht => hne ht)
  have hiRec : IntervalIntegrable (fun t : ℝ => F' t / t) volume (M : ℝ) n := by
    simpa only [div_eq_mul_inv, one_mul] using hi.mul_continuousOn hci
  have hiFloor := reciprocal_floor_integrable hM hMn hi
  have hi12 : IntervalIntegrable (fun t : ℝ => (n : ℝ) * (F' t / t) -
      F' t * (⌊(n : ℝ) / t⌋₊ : ℝ)) volume (M : ℝ) n :=
    (hiRec.const_mul _).sub hiFloor
  have he : (∫ t in (M : ℝ)..n, F' t * psi ((n : ℝ) / t)) =
      ∫ t in (M : ℝ)..n, (n : ℝ) * (F' t / t) -
        F' t * (⌊(n : ℝ) / t⌋₊ : ℝ) - (1 / 2 : ℝ) * F' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 < t := by
      rw [uIcc_of_le hMnR] at ht
      exact hMR.trans_le ht.1
    unfold psi Int.fract
    dsimp only
    rw [← natCast_floor_eq_intCast_floor (by positivity : (0 : ℝ) ≤ (n : ℝ) / t)]
    ring
  rw [he, intervalIntegral.integral_sub hi12 (hi.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_sub (hiRec.const_mul (n : ℝ)) hiFloor,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    derivative_reciprocal_integral hMR hMnR hd hc,
    derivative_reciprocal_floor_integral hM hMn hd hc,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by simpa only [uIcc_of_le hMnR] using ht)) hi]
  unfold tailFunctional
  rw [psi_nat_ratio]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul]
  field_simp
  ring

end NField.Alignment.StationarySmoothTailFunctional
