/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTwistDerivatives

/-! # The complete sum of Fourier twists from the actual derivative arc -/

noncomputable section

namespace NField.Alignment.CommonResetTwistMass

open scoped BigOperators
open Set CommonResetDerivativeSmooth CommonResetDerivativeIntervals CommonResetTwistDerivatives
open CommonResetCircleDistance CommonResetGridDistances

/-- Title: `All linear twists satisfy the complete harmonic slope bound`. -/
theorem sum_linear_twists_harmonic (f g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {u : ℕ} (hu : 0 < u) {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    (∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖) ≤
      10*(A+1)*((A+1)*(u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 4/Real.sqrt lam) +
        8*(u : ℝ)*(harmonic u : ℝ) := by
  classical
  let lo := -g (a+N)
  let hi := -g a
  let s := Real.sqrt lam
  let C := 10*(A+1)
  have hs : 0 < s := Real.sqrt_pos.mpr hlam
  have hsq : s^2 = lam := Real.sq_sqrt hlam.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmono := derivative_monotone_of_curvature g k hlam.le hg hgk hk
  have horder : lo ≤ hi := by
    have hh := hmono (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem (le_refl N)) (by simp)
    dsimp [lo, hi]
    simpa using neg_le_neg hh
  have hvar : hi-lo ≤ A*lam*N := by
    have hv := (derivative_variation g k hg hgk hk
      (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem (le_refl N)) (by simp)).2
    dsimp [lo, hi]
    simp only [Nat.cast_zero, add_zero, add_sub_cancel_left] at hv
    linarith
  have hnear_u : ((nearGrid u lo hi).card : ℝ) ≤ u := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun h : ℕ => arcDistance lo hi ((h : ℝ)/u) ≤ 1/u) (Finset.range u))).trans_eq
        (Finset.card_range u)
  have hnear_arc := near_grid_count hu horder
  have hnear : (∑ h ∈ nearGrid u lo hi, ‖linearTwistSum f a N u h‖) ≤
      C*((A+1)*(u : ℝ)*((N : ℝ)+1)*s+4/s) := by
    have hfirst : ((nearGrid u lo hi).card : ℝ)*(((N : ℝ)+1)*s) ≤
        (u : ℝ)*(((N : ℝ)+1)*s) := mul_le_mul_of_nonneg_right hnear_u (by positivity)
    have hvaru : (u : ℝ)*(hi-lo) ≤ A*(u : ℝ)*((N : ℝ)+1)*s^2 := by
      have hvu := mul_le_mul_of_nonneg_left hvar (show (0 : ℝ) ≤ u by positivity)
      rw [hsq]
      have hnon : 0 ≤ A*(u : ℝ)*lam := by positivity
      nlinarith
    have hsecond : ((nearGrid u lo hi).card : ℝ)/s ≤
        A*(u : ℝ)*((N : ℝ)+1)*s+4/s := by
      have hb := div_le_div_of_nonneg_right (hnear_arc.trans (add_le_add hvaru (le_refl 4))) hs.le
      calc
        _ ≤ (A*(u : ℝ)*((N : ℝ)+1)*s^2+4)/s := hb
        _ = _ := by field_simp
    calc
      _ ≤ ∑ _h ∈ nearGrid u lo hi, C*(((N : ℝ)+1)*s+1/s) :=
        Finset.sum_le_sum (fun h _ => linear_twist_second_bound f g k a N u h hlam hA hf hfg hg hgk hk)
      _ = C*(((nearGrid u lo hi).card : ℝ)*(((N : ℝ)+1)*s) +
          ((nearGrid u lo hi).card : ℝ)/s) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ C*((u : ℝ)*(((N : ℝ)+1)*s) + A*(u : ℝ)*((N : ℝ)+1)*s+4/s) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith
      _ = _ := by ring
  have hfar : (∑ h ∈ farGrid u lo hi, ‖linearTwistSum f a N u h‖) ≤
      8*(u : ℝ)*(harmonic u : ℝ) := by
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    calc
      _ ≤ ∑ h ∈ farGrid u lo hi, 2/arcDistance lo hi ((h : ℝ)/u) := by
        apply Finset.sum_le_sum
        intro h hh
        exact linear_twist_first_bound f g a N u h hf hfg hmono
          ((one_div_pos.mpr huR).trans (Finset.mem_filter.mp hh).2)
      _ = 2*∑ h ∈ farGrid u lo hi, 1/arcDistance lo hi ((h : ℝ)/u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ ≤ 2*(4*(u : ℝ)*(harmonic u : ℝ)) :=
        mul_le_mul_of_nonneg_left (distant_grid_sum hu horder) (by norm_num)
      _ = _ := by ring
  have hsplit : (∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖) =
      (∑ h ∈ nearGrid u lo hi, ‖linearTwistSum f a N u h‖) +
        ∑ h ∈ farGrid u lo hi, ‖linearTwistSum f a N u h‖ := by
    simpa only [nearGrid, farGrid, not_le] using
      (Finset.sum_filter_add_sum_filter_not (Finset.range u)
        (fun h : ℕ => arcDistance lo hi ((h : ℝ)/u) ≤ 1/u)
        (fun h => ‖linearTwistSum f a N u h‖)).symm
  rw [hsplit]
  exact add_le_add hnear hfar

theorem harmonic_le_twice_log {u : ℕ} (hu : 0 < u) :
    (harmonic u : ℝ) ≤ 2*Real.log (2*(u : ℝ)) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog := Real.log_nonneg hu1
  have ht := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at ht
  rw [Real.log_mul (by norm_num) huR.ne']
  have hb := harmonic_le_one_add_log u
  linarith

/-- Title: `The complete linear-twist sum has the published square-root and logarithmic bound`. -/
theorem sum_linear_twists (f g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {u : ℕ} (hu : 0 < u) {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    (∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖) ≤
      40*(A+1)^2*((u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 1/Real.sqrt lam +
        (u : ℝ)*Real.log (2*(u : ℝ))) := by
  have hb := sum_linear_twists_harmonic f g k a N hu hlam hA hf hfg hg hgk hk
  have hlog := harmonic_le_twice_log hu
  have hlog0 : 0 ≤ Real.log (2*(u : ℝ)) := Real.log_nonneg (by
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
    linarith)
  have hC1 : 1 ≤ A+1 := by linarith
  have hC2 : A+1 ≤ (A+1)^2 := by nlinarith
  have hC3 : 1 ≤ (A+1)^2 := hC1.trans hC2
  calc
    _ ≤ 10*(A+1)*((A+1)*(u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 4/Real.sqrt lam) +
        8*(u : ℝ)*(harmonic u : ℝ) := hb
    _ ≤ 10*(A+1)*((A+1)*(u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 4/Real.sqrt lam) +
        16*((u : ℝ)*Real.log (2*(u : ℝ))) := by
      apply add_le_add (le_refl _)
      have hh := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 8*(u : ℝ) by positivity)
      nlinarith
    _ = 10*(A+1)^2*((u : ℝ)*((N : ℝ)+1)*Real.sqrt lam) +
        40*(A+1)*(1/Real.sqrt lam) + 16*((u : ℝ)*Real.log (2*(u : ℝ))) := by ring
    _ ≤ 40*(A+1)^2*((u : ℝ)*((N : ℝ)+1)*Real.sqrt lam) +
        40*(A+1)^2*(1/Real.sqrt lam) +
        40*(A+1)^2*((u : ℝ)*Real.log (2*(u : ℝ))) := by
      apply add_le_add
      · apply add_le_add
        · gcongr
          nlinarith
        · gcongr
      · apply mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg (by positivity) hlog0)
    _ = _ := by ring

end NField.Alignment.CommonResetTwistMass
