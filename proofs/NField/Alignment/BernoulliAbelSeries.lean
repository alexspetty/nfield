/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BernoulliAbelPhase

/-! # The absolutely convergent regularized Bernoulli Fourier series -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliAbelSeries
open scoped ComplexConjugate
open Complex BernoulliAbelPhase

def abelTerm (ρ y : ℝ) (j : ℤ) : ℂ :=
  (ρ : ℂ)^j.natAbs * exp (-2*(Real.pi : ℂ)*I*j*y)/(2*(Real.pi : ℂ)*I*j)

theorem positive_abel_hasSum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : ℝ) :
    HasSum (fun n : ℕ => abelTerm ρ y n)
      (-log (1-(ρ : ℂ)*unitPhase y)/(2*(Real.pi : ℂ)*I)) := by
  have hz : ‖(ρ : ℂ)*unitPhase y‖ < 1 := by
    rw [norm_mul,unitPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ0]
    exact hρ1
  have h := (Complex.hasSum_taylorSeries_neg_log hz).div_const (2*(Real.pi : ℂ)*I)
  have he : (fun n : ℕ => abelTerm ρ y n)=
      (fun n : ℕ => (((ρ : ℂ)*unitPhase y)^n/n)/(2*(Real.pi : ℂ)*I)) := by
    funext n
    unfold abelTerm unitPhase
    simp only [Int.natAbs_natCast,Int.cast_natCast,mul_pow,← Complex.exp_nat_mul]
    rw [show (n : ℂ)*(-2*(Real.pi : ℂ)*I*y) = -2*(Real.pi : ℂ)*I*n*y by ring]
    simp only [div_div]
    congr 1
    ring
  rw [he]
  exact h

theorem negative_abel_conjugate (ρ y : ℝ) (n : ℕ) :
    abelTerm ρ y (- (n : ℤ)) = conj (abelTerm ρ y (n : ℤ)) := by
  unfold abelTerm
  simp only [Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast,
    map_div₀,map_mul,map_pow,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    map_neg,Complex.conj_natCast,map_ofNat,mul_neg,neg_mul,neg_neg]

theorem logarithmic_pair_value (z : ℂ) :
    -z/(2*(Real.pi : ℂ)*I) + conj (-z/(2*(Real.pi : ℂ)*I)) =
      ((-z.im/Real.pi : ℝ) : ℂ) := by
  rw [Complex.add_conj]
  congr 1
  simp only [Complex.div_re,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero,mul_one,add_zero,
    zero_add,Complex.normSq_apply]
  field_simp [Real.pi_ne_zero]
  ring

/-- Title: `The logarithmic value of the regularized Bernoulli series`. -/
theorem abel_hasSum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : ℝ) :
    HasSum (abelTerm ρ y) ((-(log (1-(ρ : ℂ)*unitPhase y)).im/Real.pi : ℝ) : ℂ) := by
  have hp := positive_abel_hasSum hρ0 hρ1 y
  have hn := Complex.hasSum_conj'.mpr hp
  have he : (fun n : ℕ => abelTerm ρ y (- (n : ℤ))) =
      (fun n : ℕ => conj (abelTerm ρ y (n : ℤ))) := funext (negative_abel_conjugate ρ y)
  rw [← he] at hn
  have h := hp.of_nat_of_neg hn
  simpa only [abelTerm,Int.natAbs_zero,Int.cast_zero,pow_zero,mul_zero,div_zero,sub_zero,
    logarithmic_pair_value] using h

theorem abel_tsum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : ℝ) :
    (∑' j : ℤ, abelTerm ρ y j) =
      ((-(log (1-(ρ : ℂ)*unitPhase y)).im/Real.pi : ℝ) : ℂ) :=
  (abel_hasSum hρ0 hρ1 y).tsum_eq

end NField.Alignment.BernoulliAbelSeries
