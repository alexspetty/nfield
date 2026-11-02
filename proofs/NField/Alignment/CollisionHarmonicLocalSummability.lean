/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicLocalExpansion

/-!
# A summable uniform harmonic-local remainder

The divisor majorant is a product of the positive zeta-two and zeta-three
series. Absolute convergence precedes every use of its infinite sum.
The resulting constant applies to arbitrary finite divisor sets and to
every alignment gcd weight, uniformly in the modulus.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicLocalSummability

open scoped Classical
open CollisionHarmonicLocalExpansion CollisionHarmonicSeed CollisionZetaMoments

theorem harmonicLocalErrorBound_nonneg (k : ℕ) : 0 ≤ harmonicLocalErrorBound k := by
  unfold harmonicLocalErrorBound
  positivity

theorem harmonicLocalErrorBound_convolution (k : ℕ) :
    harmonicLocalErrorBound k=
      (∑ d ∈ k.divisors, powerKernel 2 d*powerKernel 3 (k/d))/12 := by
  by_cases hk : k=0
  · simp [hk,harmonicLocalErrorBound]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold harmonicLocalErrorBound
  rw [Finset.sum_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  unfold powerKernel
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

theorem harmonicLocalErrorBound_hasSum :
    HasSum harmonicLocalErrorBound (zetaNat 2*zetaNat 3/12) := by
  have h2 := powerKernel_summable (by norm_num : 1 < (2 : ℕ))
  have h3 := powerKernel_summable (by norm_num : 1 < (3 : ℕ))
  have hs := h2.mul_of_nonneg h3 (powerKernel_nonneg 2) (powerKernel_nonneg 3)
  have hx : HasSum (fun p : ℕ×ℕ => powerKernel 2 p.1*powerKernel 3 p.2)
      (zetaNat 2*zetaNat 3) := h2.hasSum.mul h3.hasSum hs
  have hf := hx.tsum_fiberwise (fun p : ℕ×ℕ => p.1*p.2)
  have hb : HasSum (fun k : ℕ => ∑ d ∈ k.divisors, powerKernel 2 d*powerKernel 3 (k/d))
      (zetaNat 2*zetaNat 3) := by
    convert! hf using 1
    funext k
    exact (divisor_product_fiber (powerKernel 2) (powerKernel 3)
      (by simp [powerKernel]) (by simp [powerKernel]) k).symm
  convert! hb.div_const 12 using 1
  funext k
  exact harmonicLocalErrorBound_convolution k

theorem harmonicLocalError_summable : Summable harmonicLocalError :=
  Summable.of_norm_bounded harmonicLocalErrorBound_hasSum.summable
    (fun k => by simpa only [Real.norm_eq_abs] using harmonic_local_error_bound k)

theorem harmonicLocalError_absolute_bound :
    (∑' k : ℕ, |harmonicLocalError k|) ≤ zetaNat 2*zetaNat 3/12 := by
  have h := Summable.tsum_le_tsum harmonic_local_error_bound
    harmonicLocalError_summable.abs harmonicLocalErrorBound_hasSum.summable
  rwa [harmonicLocalErrorBound_hasSum.tsum_eq] at h

theorem harmonicLocalError_finite_bound (s : Finset ℕ) :
    |∑ k ∈ s, harmonicLocalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  calc
    _ ≤ ∑ k ∈ s, |harmonicLocalError k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, harmonicLocalErrorBound k :=
      Finset.sum_le_sum (fun k _ => harmonic_local_error_bound k)
    _ ≤ ∑' k : ℕ, harmonicLocalErrorBound k :=
      harmonicLocalErrorBound_hasSum.summable.sum_le_tsum s
        (fun k _ => harmonicLocalErrorBound_nonneg k)
    _ = _ := harmonicLocalErrorBound_hasSum.tsum_eq

theorem weighted_harmonicLocalError_norm_bound (a : ℕ → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (k : ℕ) :
    ‖a k*harmonicLocalError k‖ ≤ harmonicLocalErrorBound k := by
  rw [Real.norm_eq_abs,abs_mul]
  simpa only [one_mul] using mul_le_mul (ha k) (harmonic_local_error_bound k)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem weighted_harmonicLocalError_summable (a : ℕ → ℝ)
    (ha : ∀ k, |a k| ≤ 1) : Summable (fun k => a k*harmonicLocalError k) :=
  Summable.of_norm_bounded harmonicLocalErrorBound_hasSum.summable
    (weighted_harmonicLocalError_norm_bound a ha)

theorem weighted_harmonicLocalError_sum_bound (a : ℕ → ℝ)
    (ha : ∀ k, |a k| ≤ 1) :
    |∑' k : ℕ, a k*harmonicLocalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded harmonicLocalErrorBound_hasSum
    (weighted_harmonicLocalError_norm_bound a ha)

theorem alignment_gcd_ratio_bound (L k : ℕ) : |(k.gcd L : ℝ)/(k : ℝ)| ≤ 1 := by
  by_cases hk : k=0
  · simp [hk]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one hkR).mpr
  exact_mod_cast Nat.gcd_le_left L (Nat.pos_of_ne_zero hk)

theorem alignment_harmonicLocalError_summable (L : ℕ) :
    Summable (fun k : ℕ => (k.gcd L : ℝ)/(k : ℝ)*harmonicLocalError k) :=
  weighted_harmonicLocalError_summable _ (alignment_gcd_ratio_bound L)

theorem alignment_harmonicLocalError_uniform_bound (L : ℕ) :
    |∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicLocalError k| ≤ zetaNat 2*zetaNat 3/12 :=
  weighted_harmonicLocalError_sum_bound _ (alignment_gcd_ratio_bound L)

end NField.Alignment.CollisionHarmonicLocalSummability
