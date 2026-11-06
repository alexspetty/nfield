/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionComplexPhaseEnclosure
import NField.Alignment.CollisionDirichletRationalEnclosure
import NField.Alignment.CollisionHarmonicRootSeries

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionComplexSeriesEnclosure
open scoped BigOperators
open CollisionComplexPhaseEnclosure CollisionFourierEnclosure
open CollisionHarmonicRootSeries CollisionDirichletRationalEnclosure CollisionPositiveConstants

theorem real_scale_enclosure {z : ℂ} {x rl ru il iu l u : ℝ}
    (hz : rectangleContains z rl ru il iu) (hx : l ≤ x ∧ x ≤ u) :
    rectangleContains ((x : ℂ)*z)
      (productLower rl ru l u) (productUpper rl ru l u)
      (productLower il iu l u) (productUpper il iu l u) := by
  have hr := product_interval ⟨hz.1,hz.2.1⟩ hx
  have hi := product_interval ⟨hz.2.2.1,hz.2.2.2⟩ hx
  simp only [rectangleContains,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  simpa only [mul_comm] using And.intro hr.1 (And.intro hr.2 hi)

theorem norm_error_rectangle {z p : ℂ} {B rl ru il iu : ℝ}
    (hp : rectangleContains p rl ru il iu) (h : ‖z-p‖ ≤ B) :
    rectangleContains z (rl-B) (ru+B) (il-B) (iu+B) := by
  have hr := abs_le.mp ((Complex.abs_re_le_norm (z-p)).trans h)
  have hi := abs_le.mp ((Complex.abs_im_le_norm (z-p)).trans h)
  simp only [Complex.sub_re,Complex.sub_im] at hr hi
  rcases hp with ⟨h1,h2,h3,h4⟩
  exact ⟨by linarith [hr.1],by linarith [hr.2],by linarith [hi.1],by linarith [hi.2]⟩

theorem norm_series_tail_bound {f : ℕ → ℂ} (hf : Summable f) (N : ℕ)
    {g : ℕ → ℝ} (hg : Summable g) {B : ℝ}
    (hfg : ∀ n, ‖f (n+N+1)‖ ≤ g n) (hgB : (∑' n,g n) ≤ B) :
    ‖(∑' n,f n)-(∑ n∈Finset.range (N+1),f n)‖ ≤ B := by
  have ht : Summable (fun n : ℕ => f (n+N+1)) :=
    hf.comp_injective (fun a b h => by omega)
  have hs := hf.sum_add_tsum_nat_add (N+1)
  simp only [← Nat.add_assoc] at hs
  rw [← hs,add_sub_cancel_left]
  exact ((norm_tsum_le_tsum_norm ht.norm).trans (ht.norm.tsum_le_tsum hfg hg)).trans hgB

theorem reciprocal_square_tail {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ,1/((n+N+1 : ℕ) : ℝ)^2) ≤ 1/(N : ℝ) := by
  have h := zeta_tail_bound (by norm_num : (1 : ℝ)<2) hN
  have he (n : ℕ) : CollisionDivisorSeries.zetaKernel 2 n=1/(n : ℝ)^2 := by
    simpa using zetaKernel_nat (by norm_num : 0<(2 : ℕ)) n
  simp_rw [he] at h
  norm_num only [show (1 : ℝ)-2= -1 by norm_num,show (2 : ℝ)-1=1 by norm_num,
    Real.rpow_neg_one,div_one] at h
  simpa only [one_div] using h

theorem real_series_tail_bound {f : ℕ → ℝ} (hf : Summable f) (N : ℕ)
    {g : ℕ → ℝ} (hg : Summable g) {B : ℝ}
    (hfg : ∀ n, ‖f (n+N+1)‖ ≤ g n) (hgB : (∑' n,g n) ≤ B) :
    |(∑' n,f n)-(∑ n∈Finset.range (N+1),f n)| ≤ B := by
  have ht : Summable (fun n : ℕ => f (n+N+1)) :=
    hf.comp_injective (fun a b h => by omega)
  have hs := hf.sum_add_tsum_nat_add (N+1)
  simp only [← Nat.add_assoc] at hs
  rw [← hs,add_sub_cancel_left,← Real.norm_eq_abs]
  exact ((norm_tsum_le_tsum_norm ht.norm).trans (ht.norm.tsum_le_tsum hfg hg)).trans hgB

theorem real_error_interval {x p B l u : ℝ}
    (hp : l ≤ p ∧ p ≤ u) (h : |x-p| ≤ B) : l-B ≤ x ∧ x ≤ u+B := by
  have he := abs_le.mp h
  constructor <;> linarith [hp.1,hp.2,he.1,he.2]

end NField.Alignment.CollisionComplexSeriesEnclosure
