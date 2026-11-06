/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPolynomialMomentBox

/-! # Exact separation of the real polynomial frequency box -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealPolynomialFrequency
open scoped BigOperators Classical
open RealBilinearMoment RealPolynomialMomentBox VinogradovDiagonal

def linearKernel (β : ℝ) (K : ℕ) : ℝ :=
  ∑ v ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
    ‖∑ u ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), realCharacter (β*(u:ℝ)*(v:ℝ))‖

theorem linearKernel_nonneg (β : ℝ) (K : ℕ) : 0 ≤ linearKernel β K := by
  unfold linearKernel
  positivity

theorem box_character_sum {n : ℕ} (β : Fin n → ℝ) (H s : ℕ) (v : Fin n → ℤ) :
    (∑ u ∈ momentBox H s n, bilinearCharacter β u v) =
      ∏ j, ∑ t ∈ Finset.Icc (-(s*(H:ℤ)^(j.val+1))) (s*(H:ℤ)^(j.val+1)),
        realCharacter (β j*(t:ℝ)*(v j:ℝ)) := by
  simp only [bilinearCharacter_apply, character_sum, momentBox]
  exact (Finset.prod_univ_sum
    (fun j : Fin n => Finset.Icc (-(s*(H:ℤ)^(j.val+1))) (s*(H:ℤ)^(j.val+1)))
    (fun (j : Fin n) (t : ℤ) => realCharacter (β j*(t:ℝ)*(v j:ℝ)))).symm

theorem box_kernel_factorization {n : ℕ} (β : Fin n → ℝ) (H s : ℕ) :
    (∑ v ∈ momentBox H s n, ‖∑ u ∈ momentBox H s n, bilinearCharacter β u v‖) =
      ∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1)) := by
  simp_rw [box_character_sum, norm_prod]
  unfold momentBox linearKernel
  simp only [Nat.cast_mul, Nat.cast_pow]
  exact (Finset.prod_univ_sum
    (fun j : Fin n => Finset.Icc (-(s*(H:ℤ)^(j.val+1))) (s*(H:ℤ)^(j.val+1)))
    (fun (j : Fin n) (v : ℤ) =>
      ‖∑ u ∈ Finset.Icc (-(s*(H:ℤ)^(j.val+1))) (s*(H:ℤ)^(j.val+1)),
        realCharacter (β j*(u:ℝ)*(v:ℝ))‖)).symm

/-- No analytic bound has been assumed: the literal real-phase bilinear sum
is bounded by the existing integer Vinogradov count and one-dimensional kernels. -/
theorem polynomial_bilinear_product_bound {n : ℕ} (β : Fin n → ℝ)
    (H s : ℕ) (hs : 1 ≤ s) :
    ‖polynomialBilinear β H‖^(4*s^2) ≤
      (H:ℝ)^(4*s*(2*s-1))*(momentCount (Finset.Icc 1 (H:ℤ)) s n : ℝ)^2*
        ∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1)) := by
  simpa only [box_kernel_factorization] using polynomial_bilinear_moment_bound β H s hs

end NField.Alignment.RealPolynomialFrequency
