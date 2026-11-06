/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.IntervalFourierDecay
import NField.Alignment.SignedMultipleInverse

/-!
# Absolute recovery of the positive Fourier coefficients

For a twice continuously differentiable interval function with equal endpoint
values, the positive coefficients are determined by their sums over multiples.
The identification of these sums with angular grid readouts is a separate step.
-/

noncomputable section

namespace NField.Alignment.AngularCoefficientInverse

open scoped BigOperators
open Set IntervalFourierDecay SignedMultipleInverse

def positiveCoefficient (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else coefficient f (n : ℤ)

/-- Title: `Positive Fourier coefficients satisfy a quadratic decay bound`. -/
theorem positive_coefficient_quadratic_bound (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hend : f 1 = f 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖positiveCoefficient f n‖ ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := cont_diff_two_coefficient_decay f hf hend
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [positiveCoefficient, hn]
  · simpa only [positiveCoefficient, if_neg hn] using hb n (Nat.pos_of_ne_zero hn)

/-- Title: `The positive Fourier coefficients converge absolutely`. -/
theorem positive_coefficients_norm_summable (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hend : f 1 = f 0) :
    Summable (fun n => ‖positiveCoefficient f n‖) := by
  obtain ⟨_, _, hb⟩ := positive_coefficient_quadratic_bound f hf hend
  exact quadratic_decay_norm_summable _ hb

/-- Title: `Positive Fourier coefficients recovered from sums over multiples`. -/
theorem coefficient_multiple_inverse (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hend : f 1 = f 0)
    {n : ℕ} (hn : 0 < n) :
    coefficient f (n : ℤ) = ∑' j,
      (ArithmeticFunction.moebius j : ℝ) • multipleAmplitude (positiveCoefficient f) (n * j) := by
  obtain ⟨_, _, hb⟩ := positive_coefficient_quadratic_bound f hf hend
  simpa only [positiveCoefficient, if_neg hn.ne'] using
    quadratic_decay_multiple_inverse (positiveCoefficient f) hb hn

/-- Title: `The Fourier coefficient inverse converges absolutely`. -/
theorem coefficient_inverse_absolutely_summable (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hend : f 1 = f 0)
    {n : ℕ} (hn : 0 < n) :
    Summable (fun j =>
      ‖(ArithmeticFunction.moebius j : ℝ) • multipleAmplitude (positiveCoefficient f) (n * j)‖) := by
  obtain ⟨_, _, hb⟩ := positive_coefficient_quadratic_bound f hf hend
  exact inverse_series_norm_summable _ hb hn

/-- Title: `Multiple readouts determine every positive Fourier coefficient`. -/
theorem multiple_readouts_determine_positive_coefficients (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hg : ContDiffOn ℝ 2 g (Icc 0 1))
    (hfend : f 1 = f 0) (hgend : g 1 = g 0)
    (hread : ∀ n, multipleAmplitude (positiveCoefficient f) n =
      multipleAmplitude (positiveCoefficient g) n)
    {n : ℕ} (hn : 0 < n) : coefficient f (n : ℤ) = coefficient g (n : ℤ) := by
  rw [coefficient_multiple_inverse f hf hfend hn, coefficient_multiple_inverse g hg hgend hn]
  simp only [hread]

end NField.Alignment.AngularCoefficientInverse
