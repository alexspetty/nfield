/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindInverseResidueTransform

/-!
# The finite sawtooth sine transform

The exact finite Fourier coefficient gives the cotangent expression.
Modulo reduction covers every natural frequency, and the divisible case
vanishes. This is the finite transform used in the mixed-moment proof.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionFiniteSineTransform

open scoped BigOperators
open DedekindFourierMoment DedekindReciprocity DedekindInverseResidueTransform

def finiteSineTransform (q n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 q, ((a : ℝ)/(q : ℝ)-1/2)*
    Real.sin (2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ))

theorem negativeRoot_pow_im (q n a : ℕ) :
    (negativeRoot q n^a).im = -Real.sin (2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ)) := by
  rw [negativeRoot, ← Complex.exp_nat_mul]
  have he : (a : ℂ)*(-(2*(Real.pi : ℂ)*Complex.I*(n : ℂ)/(q : ℂ))) =
      ((-(2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ)) : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

theorem sawtoothFourier_im {q : ℕ} (hq : 0<q) (n : ℕ) :
    (sawtoothFourier q n).im= -finiteSineTransform q n := by
  rw [sawtoothFourier, Complex.im_sum,
    sum_range_eq_sum_Ico_one _ hq (by simp [rationalSawtooth_zero])]
  rw [finiteSineTransform, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hc : ((rationalSawtooth a q : ℚ) : ℂ)=(a : ℂ)/(q : ℂ)-1/2 := by
    rw [rationalSawtooth_of_lt (Finset.mem_Ico.mp ha).1 (Finset.mem_Ico.mp ha).2]
    push_cast
    rfl
  rw [hc]
  simp [Complex.mul_im, negativeRoot_pow_im]

theorem finiteSineTransform_reduced {q n : ℕ} (hq : 0<q) (hn : 0<n) (hnq : n<q) :
    finiteSineTransform q n= -(1/2 : ℝ)*Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) := by
  have h := congrArg Complex.im (sawtoothFourier_eq_cotangent hq hn hnq)
  have hc : Complex.cot ((Real.pi : ℂ)*((n : ℂ)/(q : ℂ)))=
      (Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cot]
    congr 1
    push_cast
    ring
  rw [sawtoothFourier_im hq, hc] at h
  norm_num only [Complex.mul_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
    Complex.I_im, Complex.I_re, Complex.ofReal_im, Complex.ofReal_re,
    mul_zero, zero_add] at h
  linarith

theorem sawtoothFourier_mod {q : ℕ} (hq : 0<q) (n : ℕ) :
    sawtoothFourier q (n%q)=sawtoothFourier q n := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp only [sawtoothFourier, negativeRoot_eq_stdAddChar, ZMod.natCast_mod]

theorem finiteSineTransform_mod {q : ℕ} (hq : 0<q) (n : ℕ) :
    finiteSineTransform q (n%q)=finiteSineTransform q n := by
  have h := congrArg Complex.im (sawtoothFourier_mod hq n)
  simpa only [sawtoothFourier_im hq, neg_inj] using h

theorem cotangent_mod {q : ℕ} (hq : 0<q) (n : ℕ) :
    Real.cot (Real.pi*((n%q : ℕ) : ℝ)/(q : ℝ))=
      Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) := by
  have hp : Function.Periodic Real.cot Real.pi := by
    simpa only [Function.comp_def, Real.tan_inv_eq_cot] using
      Real.tan_periodic.comp (fun x : ℝ => x⁻¹)
  have h := hp.nat_mul (n/q) (Real.pi*((n%q : ℕ) : ℝ)/(q : ℝ))
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have he : Real.pi*((n%q : ℕ) : ℝ)/(q : ℝ)+((n/q : ℕ) : ℝ)*Real.pi =
      Real.pi*(n : ℝ)/(q : ℝ) := by
    have hn : ((n%q : ℕ) : ℝ)+(q : ℝ)*((n/q : ℕ) : ℝ)=(n : ℝ) := by
      exact_mod_cast Nat.mod_add_div n q
    field_simp
    nlinarith [congrArg (fun x : ℝ => Real.pi*x) hn]
  rw [he] at h
  exact h.symm

theorem literal_finite_sine_transform {q : ℕ} (hq : 0<q) (n : ℕ) :
    finiteSineTransform q n=
      if q ∣ n then 0 else -(1/2 : ℝ)*Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) := by
  rw [← finiteSineTransform_mod hq n]
  by_cases hn : q ∣ n
  · rw [if_pos hn, Nat.mod_eq_zero_of_dvd hn]
    simp [finiteSineTransform]
  · rw [if_neg hn, finiteSineTransform_reduced hq
      (Nat.pos_of_ne_zero (fun h => hn (Nat.dvd_of_mod_eq_zero h))) (Nat.mod_lt n hq),
      cotangent_mod hq]

end NField.Alignment.CollisionFiniteSineTransform
