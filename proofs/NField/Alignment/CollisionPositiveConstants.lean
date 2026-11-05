/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDivisorSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rational constants for the positive Mobius regrouping

Finite rational sums certify lower bounds for the full positive zeta series.
The three-halves upper bound uses a proved infinite integral tail. These
constants are applied to the actual divisor-deficit series formula.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositiveConstants

open scoped BigOperators Classical
open MeasureTheory Set
open CollisionDivisorSeries

theorem zetaKernel_nat {p : ℕ} (hp : 0 < p) (n : ℕ) :
    zetaKernel (p : ℝ) n=1/(n : ℝ)^p := by
  rw [zetaKernel_rpow (by exact_mod_cast hp.ne'),Real.rpow_neg (Nat.cast_nonneg n),
    Real.rpow_natCast,one_div]

theorem realZeta_two : realZeta 2=Real.pi^2/6 := by
  have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).hasSum
  change HasSum (fun n => zetaKernel 2 n) (realZeta 2) at h
  have he (n : ℕ) : zetaKernel 2 n=1/(n : ℝ)^2 := zetaKernel_nat (by norm_num) n
  simp_rw [he] at h
  exact h.unique hasSum_zeta_two

theorem realZeta_four : realZeta 4=Real.pi^4/90 := by
  have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 4)).hasSum
  change HasSum (fun n => zetaKernel 4 n) (realZeta 4) at h
  have he (n : ℕ) : zetaKernel 4 n=1/(n : ℝ)^4 := zetaKernel_nat (by norm_num) n
  simp_rw [he] at h
  exact h.unique hasSum_zeta_four

theorem realZeta_two_lower : (13/8 : ℝ) < realZeta 2 := by
  have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).sum_le_tsum
    (Finset.range 51) (fun n _ => zetaKernel_nonneg 2 n)
  change (∑ n ∈ Finset.range 51, zetaKernel 2 n) ≤ realZeta 2 at h
  have he (n : ℕ) : zetaKernel 2 n=1/(n : ℝ)^2 := zetaKernel_nat (by norm_num) n
  simp_rw [he] at h
  have hc : (13/8 : ℝ) < ∑ n ∈ Finset.range 51, 1/(n : ℝ)^2 := by
    norm_num [Finset.sum_range_succ]
  exact hc.trans_le h

theorem realZeta_three_lower : (6/5 : ℝ) < realZeta 3 := by
  have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 3)).sum_le_tsum
    (Finset.range 17) (fun n _ => zetaKernel_nonneg 3 n)
  change (∑ n ∈ Finset.range 17, zetaKernel 3 n) ≤ realZeta 3 at h
  have he (n : ℕ) : zetaKernel 3 n=1/(n : ℝ)^3 := zetaKernel_nat (by norm_num) n
  simp_rw [he] at h
  have hc : (6/5 : ℝ) < ∑ n ∈ Finset.range 17, 1/(n : ℝ)^3 := by
    norm_num [Finset.sum_range_succ]
  exact hc.trans_le h

theorem threeHalves_power {x : ℝ} (hx : 0 < x) :
    x^(-(3/2 : ℝ))=1/(x*Real.sqrt x) := by
  rw [Real.rpow_neg hx.le,show (3/2 : ℝ)=1+1/2 by norm_num,
    Real.rpow_add hx,Real.rpow_one,← Real.sqrt_eq_rpow,one_div]

theorem threeHalves_tail_le_one :
    (∑' n : ℕ, zetaKernel (3/2) (n+5)) ≤ 1 := by
  have ha : AntitoneOn (fun x : ℝ => x^(-(3/2 : ℝ))) (Ici 4) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by have := hx; simp only [mem_Ici] at this; linarith)
      hxy (by norm_num)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 4)
  have ht := ha.tsum_comp_add_le_integral 4 hi (fun x hx =>
    Real.rpow_nonneg (by have := hx; simp only [mem_Ioi] at this; linarith) _)
  norm_num only [Nat.cast_ofNat] at ht
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 4)] at ht
  have he : -(4 : ℝ)^(-(3/2 : ℝ)+1)/(-(3/2 : ℝ)+1)=1 := by
    norm_num [show -(3/2 : ℝ)+1=-(1/2 : ℝ) by norm_num,
      Real.rpow_neg,← Real.sqrt_eq_rpow]
  rw [he] at ht
  convert! ht using 1

theorem threeHalves_two_bound : (2 : ℝ)^(-(3/2 : ℝ)) < 5/14 := by
  rw [threeHalves_power (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hsq : (7/5 : ℝ) < Real.sqrt 2 := by nlinarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*Real.sqrt 2)).mpr
  nlinarith

theorem threeHalves_three_bound : (3 : ℝ)^(-(3/2 : ℝ)) < 1/5 := by
  rw [threeHalves_power (by norm_num : (0 : ℝ) < 3)]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hsq : (5/3 : ℝ) < Real.sqrt 3 := by nlinarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 3*Real.sqrt 3)).mpr
  nlinarith

theorem realZeta_threeHalves_upper : realZeta (3/2) < 751/280 := by
  have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 3/2)).sum_add_tsum_nat_add 5
  have he (n : ℕ) := zetaKernel_rpow (by norm_num : (3/2 : ℝ)≠0) n
  have hp : (∑ n ∈ Finset.range 5, zetaKernel (3/2) n)=
      1+(2 : ℝ)^(-(3/2 : ℝ))+(3 : ℝ)^(-(3/2 : ℝ))+1/8 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    simp only [he]
    norm_num [threeHalves_power (by norm_num : (0 : ℝ) < 4),
      Real.zero_rpow (by norm_num : -(3/2 : ℝ)≠0)]
  rw [hp] at h
  change _+_=realZeta (3/2) at h
  linarith [threeHalves_tail_le_one,threeHalves_two_bound,threeHalves_three_bound]

theorem deficitSeries_two_exact : deficitSeries 2=7/4-realZeta 2 := by
  rw [deficitSeries_formula (by norm_num : (1 : ℝ) < 2)]
  norm_num only [show (2 : ℝ)*2=4 by norm_num]
  rw [realZeta_two,realZeta_four]
  field_simp [Real.pi_ne_zero]
  ring

theorem deficitSeries_two_upper : deficitSeries 2 < 1/8 := by
  rw [deficitSeries_two_exact]
  linarith [realZeta_two_lower]

theorem deficitSeries_threeHalves_upper : deficitSeries (3/2) < 67/80 := by
  have hz1 : (1 : ℝ) ≤ realZeta (3/2) := by
    have h := (zetaKernel_summable (by norm_num : (1 : ℝ) < 3/2)).le_tsum
      1 (fun n _ => zetaKernel_nonneg (3/2) n)
    change zetaKernel (3/2) 1 ≤ realZeta (3/2) at h
    have hone : zetaKernel (3/2) 1=1 := by simp [zetaKernel,CollisionSquarefreeEuler.realPower]
    rwa [hone] at h
  have hzu : realZeta (3/2) < 27/10 := by linarith [realZeta_threeHalves_upper]
  have hz3 := realZeta_three_lower
  have hden : 0 < 2*realZeta 3 := by linarith
  have hdiv : realZeta (3/2)^2/(2*realZeta 3) ≤ (5/12 : ℝ)*realZeta (3/2)^2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg (realZeta (3/2))) (by linarith : 0 ≤ realZeta 3-6/5)]
  rw [deficitSeries_formula (by norm_num : (1 : ℝ) < 3/2)]
  norm_num only [show (2 : ℝ)*(3/2)=3 by norm_num]
  nlinarith [mul_nonneg (by linarith : 0 ≤ realZeta (3/2)-1)
    (by linarith : 0 ≤ 27/10-realZeta (3/2))]

theorem logarithm_half_bound {x : ℝ} (hx : 0 < x) :
    (1/2 : ℝ)*Real.log x ≤ Real.exp (-1)*Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (div_pos hs (Real.exp_pos 1))
  rw [Real.log_div hs.ne' (Real.exp_ne_zero 1),Real.log_exp,Real.log_sqrt hx.le] at h
  rw [Real.exp_neg]
  simp only [div_eq_mul_inv] at h
  nlinarith

theorem exp_negative_one_upper : Real.exp (-1) < (37/100 : ℝ) := by
  rw [Real.exp_neg,inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
  linarith [Real.exp_one_gt_d9]

theorem logarithm_half_rational {x : ℝ} (hx : 0 < x) :
    (1/2 : ℝ)*Real.log x < (37/100 : ℝ)*Real.sqrt x :=
  (logarithm_half_bound hx).trans_lt
    (mul_lt_mul_of_pos_right exp_negative_one_upper (Real.sqrt_pos.mpr hx))

theorem deficitSeries_combined_upper :
    (3/2 : ℝ)*deficitSeries 2+(37/100 : ℝ)*deficitSeries (3/2) < 3979/8000 := by
  linarith [deficitSeries_two_upper,deficitSeries_threeHalves_upper]

end NField.Alignment.CollisionPositiveConstants
