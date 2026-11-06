/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # Exact period energies of finite real trigonometric polynomials -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealTrigonometricEnergy
open scoped BigOperators ComplexConjugate
open MeasureTheory

def trig (S : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, c n*fourier n (t : AddCircle (1:ℝ))

theorem continuous_trig (S : Finset ℤ) (c : ℤ → ℂ) : Continuous (trig S c) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul ((fourier n).continuous.comp (AddCircle.continuous_mk' 1))

theorem periodic_trig (S : Finset ℤ) (c : ℤ → ℂ) : Function.Periodic (trig S c) 1 := by
  intro t
  unfold trig
  congr 1
  ext n
  simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]

theorem integral_fourier (n : ℤ) :
    (∫ t in (0:ℝ)..1, fourier n (t : AddCircle (1:ℝ))) = if n=0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  rw [fourierCoeff_eq_intervalIntegral (fourier n) 0 0] at h
  simpa [fourier_zero, Pi.single_apply, eq_comm] using h

theorem energy_expansion (S : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) :
    ((‖trig S c t‖^2 : ℝ):ℂ) =
      ∑ n ∈ S, ∑ m ∈ S,
        (c n*conj (c m))*fourier (n-m) (t : AddCircle (1:ℝ)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold trig
  simp only [map_sum, Finset.sum_mul_sum, map_mul]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [sub_eq_add_neg, fourier_add, fourier_neg]
  ring

theorem integral_energy (S : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖trig S c t‖^2) = ∑ n ∈ S, ‖c n‖^2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [energy_expansion]
  have hint (n m : ℤ) : IntervalIntegrable
      (fun t : ℝ => (c n*conj (c m))*fourier (n-m) (t : AddCircle (1:ℝ)))
      volume 0 1 :=
    (continuous_const.mul ((fourier (n-m)).continuous.comp
      (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  have houter (n : ℤ) : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ S, (c n*conj (c m))*fourier (n-m) (t : AddCircle (1:ℝ)))
      volume 0 1 := by
    convert IntervalIntegrable.sum S (fun m _ => hint n m) using 1 <;>
      first | rfl | (ext t; simp only [Finset.sum_apply])
  rw [intervalIntegral.integral_finsetSum (fun n _ => houter n)]
  simp_rw [intervalIntegral.integral_finsetSum (fun m _ => hint _ m),
    intervalIntegral.integral_const_mul, integral_fourier, sub_eq_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun n hn => if_pos hn)

def trigDeriv (S : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) : ℂ :=
  trig S (fun n => c n*(2*Real.pi*Complex.I*n)) t

theorem hasDerivAt_trig (S : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (trig S c) (trigDeriv S c t) t := by
  have h := HasDerivAt.sum (fun n (_ : n ∈ S) =>
    (hasDerivAt_fourier 1 n t).const_mul (c n))
  convert h using 1 <;> first | rfl | (ext y; simp [trigDeriv, trig, mul_assoc]) |
    simp [trigDeriv, trig, mul_assoc]

theorem deriv_energy_bound (S : Finset ℤ) (c : ℤ → ℂ) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    ‖deriv (fun u => ‖trig S c u‖^2) t‖ ≤
      L*‖trig S c t‖^2 + L⁻¹*‖trigDeriv S c t‖^2 := by
  rw [((hasDerivAt_trig S c t).norm_sq).deriv, norm_mul,
    Real.norm_ofNat, Real.norm_eq_abs]
  have ha := abs_real_inner_le_norm (trig S c t) (trigDeriv S c t)
  have hsq := sq_nonneg (L*‖trig S c t‖-‖trigDeriv S c t‖)
  have hc : 2*‖trig S c t‖*‖trigDeriv S c t‖ ≤
      L*‖trig S c t‖^2+L⁻¹*‖trigDeriv S c t‖^2 := by
    apply (mul_le_mul_iff_right₀ hL).mp
    field_simp
    nlinarith
  nlinarith

end NField.Alignment.RealTrigonometricEnergy
