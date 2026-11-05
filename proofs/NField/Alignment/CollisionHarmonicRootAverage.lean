/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicRootIdentity
import NField.Alignment.CollisionFiniteSineTransform
import NField.Alignment.CollisionCotangentSeries
import NField.Alignment.CollisionRamanujan

/-!
# Averaging the harmonic-root identity

The average uses every actual q-th root, including one. Absolute
convergence justifies each finite/infinite interchange; the finite sine
transform then gives the actual cotangent series.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicRootAverage

open scoped BigOperators
open CollisionHarmonicRootSeries CollisionHarmonicRootIdentity CollisionHarmonicSeed
open CollisionAmplitudeArithmetic CollisionFiniteSineTransform CollisionCotangentSeries

def rootAngle (q a : ℕ) : ℝ := 2*Real.pi*(a : ℝ)/(q : ℝ)

theorem rootAngle_nonneg (q a : ℕ) : 0 ≤ rootAngle q a := by
  unfold rootAngle
  positivity

theorem rootAngle_lt_two_pi {q a : ℕ} (hq : 0<q) (ha : a<q) :
    rootAngle q a<2*Real.pi := by
  unfold rootAngle
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hq)).2
  exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr ha) (by positivity)

theorem root_power_eq_phase (q a n : ℕ) :
    Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n=CollisionRamanujan.phase q (n : ℤ) a := by
  rw [← Complex.exp_nat_mul]
  unfold rootAngle CollisionRamanujan.phase
  push_cast
  congr 1
  ring

theorem root_power_sum {q : ℕ} (hq : 0<q) (n : ℕ) :
    (∑ a ∈ Finset.range q, Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n)=
      if q∣n then (q : ℂ) else 0 := by
  simp_rw [root_power_eq_phase]
  simpa only [Int.natCast_dvd_natCast] using CollisionRamanujan.full_phase_sum hq (n : ℤ)

theorem root_series_summable {f : ℕ → ℝ} (hf : Summable f) (q a : ℕ) :
    Summable (fun n => (f n : ℂ)*Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n) := by
  apply Summable.of_norm_bounded hf.norm
  intro n
  simp only [norm_mul,Complex.norm_real,norm_pow,circle_exp_norm,one_pow,mul_one]
  exact le_rfl

theorem root_series_sum {f : ℕ → ℝ} (hf : Summable f) {q : ℕ} (hq : 0<q) :
    (∑ a ∈ Finset.range q, ∑' n, (f n : ℂ)*Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n)=
      (q : ℂ)*((∑' m, f (q*m) : ℝ) : ℂ) := by
  rw [← Summable.tsum_finsetSum (fun a _ => root_series_summable hf q a)]
  simp_rw [← Finset.mul_sum,root_power_sum hq]
  have heq (n : ℕ) : (f n : ℂ)*(if q∣n then (q : ℂ) else 0)=
      (q : ℂ)*((if q∣n then f n else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp [mul_comm]
  simp_rw [heq]
  rw [tsum_mul_left,← Complex.ofReal_tsum,← tsum_multiples hq]

theorem harmonic_root_sum {q : ℕ} (hq : 0<q) :
    (∑ a ∈ Finset.range q, harmonicBoundary (rootAngle q a))=(q : ℂ)*(harmonicSeed q : ℂ) :=
  root_series_sum harmonicKernel_hasSum.summable hq

theorem harmonic_root_re_sum {q : ℕ} (hq : 0<q) :
    (∑ a ∈ Finset.range q, (harmonicBoundary (rootAngle q a)).re)=(q : ℝ)*harmonicSeed q := by
  have h := congrArg Complex.re (harmonic_root_sum hq)
  simpa using h

theorem cubic_root_term_re (q a n : ℕ) :
    ((cubeKernel n : ℂ)*Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n).re=
      cubicCosineTerm (rootAngle q a) n := by
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    CollisionClausenDerivative.circle_power_re]
  unfold cubicCosineTerm cubeKernel
  ring

theorem cubic_root_sum {q : ℕ} (hq : 0<q) :
    (∑ a ∈ Finset.range q, cubicCosine (rootAngle q a))=
      (q : ℝ)*zetaThree/(q : ℝ)^3 := by
  have h := congrArg Complex.re (root_series_sum cubeKernel_summable hq)
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
  have hterm (a : ℕ) :
      (∑' n, (cubeKernel n : ℂ)*Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n).re=
        cubicCosine (rootAngle q a) := by
    rw [Complex.re_tsum (root_series_summable cubeKernel_summable q a)]
    simp only [cubic_root_term_re,cubicCosine]
  simp_rw [hterm] at h
  rw [tsum_multiples hq,cubeKernel_multiples hq] at h
  simpa [cubeKernel,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

theorem rootAngle_weight (q a : ℕ) :
    (rootAngle q a-Real.pi)/2=Real.pi*((a : ℝ)/(q : ℝ)-1/2) := by
  unfold rootAngle
  ring

theorem weighted_sine_root_term {q : ℕ} (hq : 0<q) (n : ℕ) :
    (∑ a ∈ Finset.range q, (rootAngle q a-Real.pi)/2*
      quadraticSineTerm (rootAngle q a) n)= -(Real.pi/2)*cotangentTerm q n := by
  have hfinite : (∑ a ∈ Finset.range q, ((a : ℝ)/(q : ℝ)-1/2)*
      Real.sin ((n : ℝ)*rootAngle q a))=finiteSineTransform q n := by
    rw [DedekindReciprocity.sum_range_eq_sum_Ico_one _ hq
      (by simp [rootAngle])]
    unfold finiteSineTransform
    apply Finset.sum_congr rfl
    intro a _
    congr 2
    unfold rootAngle
    ring
  calc
    _ = Real.pi*(∑ a ∈ Finset.range q, ((a : ℝ)/(q : ℝ)-1/2)*
        Real.sin ((n : ℝ)*rootAngle q a))/(n : ℝ)^2 := by
      rw [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [rootAngle_weight,quadraticSineTerm]
      ring
    _ = Real.pi*finiteSineTransform q n/(n : ℝ)^2 := by rw [hfinite]
    _ = _ := by
      rw [literal_finite_sine_transform hq,cotangentTerm]
      split_ifs <;> ring

theorem weighted_clausen_root_sum {q : ℕ} (hq : 0<q) :
    (∑ a ∈ Finset.range q, (rootAngle q a-Real.pi)/2*quadraticSine (rootAngle q a))=
      -(Real.pi/2)*cotangentSum q := by
  simp only [quadraticSine,← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun a _ =>
    (quadraticSineTerm_summable (rootAngle q a)).mul_left ((rootAngle q a-Real.pi)/2))]
  simp only [weighted_sine_root_term hq,tsum_mul_left,cotangentSum]

theorem literal_harmonic_root_average {q : ℕ} (hq : 0<q) :
    harmonicSeed q=zetaThree/2*(1+1/(q : ℝ)^3)-Real.pi/(2*(q : ℝ))*cotangentSum q := by
  have hsum : (∑ a ∈ Finset.range q, (harmonicBoundary (rootAngle q a)).re)=
      ∑ a ∈ Finset.range q,
        ((zetaThree+cubicCosine (rootAngle q a))/2+
          (rootAngle q a-Real.pi)/2*quadraticSine (rootAngle q a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact literal_harmonic_root_identity (rootAngle_nonneg q a)
      (rootAngle_lt_two_pi hq (Finset.mem_range.mp ha)).le
  rw [harmonic_root_re_sum hq,Finset.sum_add_distrib,weighted_clausen_root_sum hq,
    ← Finset.sum_div,Finset.sum_add_distrib,cubic_root_sum hq,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hqR : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr hq.ne'
  apply (mul_left_cancel₀ hqR)
  rw [hsum]
  field_simp
  ring

end NField.Alignment.CollisionHarmonicRootAverage
