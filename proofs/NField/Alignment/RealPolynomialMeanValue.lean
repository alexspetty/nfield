/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealKernelSaving
import NField.Alignment.VinogradovMeanValue

/-! # Real polynomial sums bounded by the actual normalized Vinogradov mean -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealPolynomialMeanValue
open scoped BigOperators
open RealPolynomialMomentBox RealPolynomialFrequency RealKernelSaving
  VinogradovDiagonal VinogradovNormalizedRecurrence VinogradovMeanValue

theorem sum_degree (n : ℕ) : (∑ j : Fin n, (j.val+1)) = weight n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have h₁ := two_mul_weight n
    have h₂ := two_mul_weight (n+1)
    nlinarith

theorem product_box_radius (s H n : ℕ) :
    (∏ j : Fin n, ((s:ℝ)*(H:ℝ)^(j.val+1))^4) =
      (s:ℝ)^(4*n)*(H:ℝ)^(4*weight n) := by
  simp only [mul_pow, ← pow_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, sum_degree]
  rw [Nat.mul_comm (weight n) 4]

theorem product_kernel_bound {n : ℕ} (β : Fin n → ℝ) (hβ : ∀ j, β j ≠ 0)
    (s H : ℕ) (hs : 1 ≤ s) (hH : 1 ≤ H) :
    (∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1))^2) ≤
      1000^n*(s:ℝ)^(4*n)*(H:ℝ)^(4*weight n)*
        ∏ j : Fin n, saving (β j) (s*H^(j.val+1)) := by
  calc
    _ ≤ ∏ j : Fin n, 1000*((s*H^(j.val+1):ℕ):ℝ)^4*
        saving (β j) (s*H^(j.val+1)) := by
      apply Finset.prod_le_prod
      · intro j _; exact sq_nonneg _
      · intro j _
        exact linearKernel_sq_saving (β j) (hβ j) _
          (Nat.mul_pos (by omega) (pow_pos (by omega) _))
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, product_box_radius]
      ring

theorem polynomial_normalized_moment_bound {n : ℕ} (β : Fin n → ℝ)
    (hβ : ∀ j, β j ≠ 0) (H s : ℕ) (hs : 1 ≤ s) (hH : 1 ≤ H)
    (hD : weight n ≤ 2*s) :
    ‖polynomialBilinear β H‖^(8*s^2) ≤
      1000^n*(s:ℝ)^(4*n)*(H:ℝ)^(16*s^2)*(mean s n H)^4*
        ∏ j : Fin n, saving (β j) (s*H^(j.val+1)) := by
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hraw := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _)
    (polynomial_bilinear_product_bound β H s hs) 2
  have hp := product_kernel_bound β hβ s H hs hH
  have hJ : (momentCount (Finset.Icc 1 (H:ℤ)) s n:ℝ) =
      mean s n H*(H:ℝ)^(2*s-weight n) := by
    exact (div_mul_cancel₀ _ (ne_of_gt (pow_pos hH0 _))).symm
  have he₁ : 4*s^2*2 = 8*s^2 := by ring
  have he₂ : 4*s*(2*s-1)*2+4*(2*s-weight n)+4*weight n = 16*s^2 := by
    have hsub := Nat.sub_add_cancel hD
    have hs' : 1 ≤ 2*s := by omega
    have hsub' := Nat.sub_add_cancel hs'
    nlinarith
  simp only [mul_pow, ← pow_mul, he₁] at hraw
  have hk : (∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1)))^2 =
      ∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1))^2 :=
    (Finset.prod_pow _ _ _).symm
  rw [hk] at hraw
  calc
    _ ≤ (H:ℝ)^(4*s*(2*s-1)*2)*
        (momentCount (Finset.Icc 1 (H:ℤ)) s n:ℝ)^(2*2)*
        ∏ j : Fin n, linearKernel (β j) (s*H^(j.val+1))^2 := hraw
    _ ≤ (H:ℝ)^(4*s*(2*s-1)*2)*
        (momentCount (Finset.Icc 1 (H:ℤ)) s n:ℝ)^4*
        (1000^n*(s:ℝ)^(4*n)*(H:ℝ)^(4*weight n)*
          ∏ j : Fin n, saving (β j) (s*H^(j.val+1))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [hJ, mul_pow, ← pow_mul]
      have he : (H:ℝ)^(4*s*(2*s-1)*2)*(H:ℝ)^((2*s-weight n)*4)*
          (H:ℝ)^(4*weight n) = (H:ℝ)^(16*s^2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc
        _ = 1000^n*(s:ℝ)^(4*n)*
            ((H:ℝ)^(4*s*(2*s-1)*2)*(H:ℝ)^((2*s-weight n)*4)*(H:ℝ)^(4*weight n))*
            (mean s n H)^4*∏ j : Fin n, saving (β j) (s*H^(j.val+1)) := by ring
        _ = _ := by rw [he]

end NField.Alignment.RealPolynomialMeanValue
