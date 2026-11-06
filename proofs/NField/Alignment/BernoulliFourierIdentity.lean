/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealCarrierGridAlias
import Mathlib.NumberTheory.ZetaValues

/-! # The absolutely convergent second Bernoulli Fourier identity -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliFourierIdentity
open RealCarrierGridAlias Complex

theorem bernoulli_two_fourier_positive (y : ℝ) :
    HasSum (fun j : ℤ => Complex.exp (2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2)
      (-(1/2:ℂ)*(bernoulliTwo y:ℂ)) := by
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k:=2) (by omega)
    (x:=Int.fract y) ⟨Int.fract_nonneg y,(Int.fract_lt_one y).le⟩
  have hmul := h.mul_left ((1:ℂ)/(2*(Real.pi:ℂ)*I)^2)
  have hc : (2*(Real.pi:ℂ)*I)≠0 := two_pi_I_ne_zero
  have hfun : (fun j : ℤ => Complex.exp (2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2)=
      (fun j : ℤ => (1:ℂ)/(2*(Real.pi:ℂ)*I)^2*
        ((1:ℂ)/(j:ℂ)^2*_root_.fourier j ((Int.fract y:ℝ):UnitAddCircle))) := by
    funext j
    rw [AddCircle.coe_fract,fourier_coe_apply]
    simp only [Complex.ofReal_one,div_one,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  have hval : -(1/2:ℂ)*(bernoulliTwo y:ℂ)=
      (1:ℂ)/(2*(Real.pi:ℂ)*I)^2*
        (-(2*(Real.pi:ℂ)*I)^2/(Nat.factorial 2:ℂ)*(bernoulliFun 2 (Int.fract y):ℂ)) := by
    rw [bernoulliFun_two]
    norm_num only [Nat.factorial_two]
    unfold bernoulliTwo
    push_cast
    field_simp
  rw [hfun,hval]
  exact hmul

/-- Title: `The second Bernoulli Fourier series at every real phase`. -/
theorem bernoulli_two_fourier (y : ℝ) :
    HasSum (fun j : ℤ => Complex.exp (-2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2)
      (-(1/2:ℂ)*(bernoulliTwo y:ℂ)) := by
  have h := (Equiv.neg ℤ).hasSum_iff.mpr (bernoulli_two_fourier_positive y)
  have he : (fun j : ℤ => Complex.exp (-2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2)=
      (fun j : ℤ => Complex.exp (2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2) ∘
        (Equiv.neg ℤ) := by
    funext j
    simp only [Function.comp_apply,Equiv.neg_apply,Int.cast_neg,mul_neg,neg_sq]
    congr 2
    ring
  rw [he]
  exact h

theorem bernoulli_two_fourier_summable (y : ℝ) :
    Summable (fun j : ℤ => Complex.exp (-2*(Real.pi:ℂ)*I*j*y)/(2*(Real.pi:ℂ)*I*j)^2) :=
  (bernoulli_two_fourier y).summable

end NField.Alignment.BernoulliFourierIdentity
