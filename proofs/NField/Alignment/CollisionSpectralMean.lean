/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralEuler
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Mean value of the spectral arithmetic weight

The finite identity counts exact divisibility in the initial integer
interval. A summable absolute correction series dominates every normalized
row, so the limit follows by dominated convergence without a prime-event
independence assumption.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralMean

open scoped BigOperators Classical ArithmeticFunction.zeta
open Filter ArithmeticFunction
open CollisionSpectralArithmetic CollisionSpectralEuler

theorem spectralWeight_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, spectralWeight n)=
      ∑ d ∈ Finset.Ioc 0 N, spectralCorrection d*((N/d : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_zeta_eq_sum spectralCorrection N
  simpa only [spectralCorrection_convolution,spectralArithmetic_apply] using h

def meanTerm (N d : ℕ) : ℝ := spectralCorrection d*((N/d : ℕ) : ℝ)/(N : ℝ)

theorem meanTerm_support (N d : ℕ) (hd : d∉Finset.Ioc 0 N) : meanTerm N d=0 := by
  by_cases hd0 : d=0
  · simp [meanTerm,hd0]
  · have hNd : N<d := by simp only [Finset.mem_Ioc] at hd; omega
    simp [meanTerm,Nat.div_eq_of_lt hNd]

theorem spectralMean_tsum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, spectralWeight n)/(N : ℝ)=∑' d, meanTerm N d := by
  rw [tsum_eq_sum (meanTerm_support N),spectralWeight_partial_sum]
  simp only [meanTerm,Finset.sum_div]

theorem nat_quotient_ratio_bound {N d : ℕ} (hN : 0<N) (hd : 0<d) :
    ((N/d : ℕ) : ℝ)/(N : ℝ)≤1/(d : ℝ) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (div_le_div_iff₀ hNR hdR).mpr
  simpa only [one_mul] using (show ((N/d : ℕ) : ℝ)*(d : ℝ)≤(N : ℝ) by
    exact_mod_cast Nat.div_mul_le_self N d)

theorem nat_quotient_ratio_error {N d : ℕ} (hN : 0<N) (hd : 0<d) :
    |((N/d : ℕ) : ℝ)/(N : ℝ)-1/(d : ℝ)|≤1/(N : ℝ) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have he : ((N/d : ℕ) : ℝ)*(d : ℝ)+((N%d : ℕ) : ℝ)=(N : ℝ) := by
    exact_mod_cast (show N/d*d+N%d=N by simpa only [Nat.mul_comm] using Nat.div_add_mod N d)
  rw [abs_of_nonpos (sub_nonpos.mpr (nat_quotient_ratio_bound hN hd))]
  apply (mul_le_mul_iff_left₀ (mul_pos hNR hdR)).mp
  calc
    _ = ((N%d : ℕ) : ℝ) := by field_simp; nlinarith [he]
    _ ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt N hd).le
    _ = (1/(N : ℝ))*((N : ℝ)*(d : ℝ)) := by field_simp

theorem nat_quotient_ratio_tendsto {d : ℕ} (hd : 0<d) :
    Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (nhds (1/(d : ℝ))) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  refine squeeze_zero (fun N => abs_nonneg _) (fun N =>
    nat_quotient_ratio_error (Nat.succ_pos N) hd) ?_
  have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  convert! h using 1
  simp only [one_div,Function.comp_def]

theorem meanTerm_norm_bound (N d : ℕ) : ‖meanTerm N d‖≤‖correctionKernel d‖ := by
  by_cases hN : N=0
  · simp [meanTerm,hN]
  by_cases hd : d=0
  · simp [meanTerm,hd]
  have h := mul_le_mul_of_nonneg_left
    (nat_quotient_ratio_bound (Nat.pos_of_ne_zero hN) (Nat.pos_of_ne_zero hd))
    (norm_nonneg (spectralCorrection d))
  simpa only [meanTerm,correctionKernel_apply,norm_div,norm_mul,Real.norm_natCast,
    mul_div_assoc,mul_one_div] using h

theorem meanTerm_tendsto (d : ℕ) :
    Tendsto (fun N => meanTerm N d) atTop (nhds (correctionKernel d)) := by
  by_cases hd : d=0
  · subst d
    simp only [meanTerm,ArithmeticFunction.map_zero,zero_mul,zero_div]
    exact tendsto_const_nhds
  · have h := (nat_quotient_ratio_tendsto (Nat.pos_of_ne_zero hd)).const_mul
      (spectralCorrection d)
    simpa only [meanTerm,correctionKernel_apply,mul_div_assoc,mul_one_div] using h

theorem spectralWeight_mean :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, spectralWeight n)/(N : ℝ))
      atTop (nhds spectralConstant) := by
  have ht := tendsto_tsum_of_dominated_convergence correctionKernel_norm_summable
    meanTerm_tendsto (Eventually.of_forall meanTerm_norm_bound)
  simp only [← spectralMean_tsum] at ht
  rw [spectralConstant_series]
  exact ht

theorem spectralWeight_real_divisor_sum (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, spectralWeight n)/x=
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, spectralCorrection d*((⌊x/(d : ℝ)⌋₊ : ℕ) : ℝ)/x := by
  rw [spectralWeight_partial_sum,Finset.sum_div]
  simp only [Nat.floor_div_natCast]

theorem spectralWeight_real_mean :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, spectralWeight n)/x)
      atTop (nhds spectralConstant) := by
  have h := (spectralWeight_mean.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hn : 0<⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hnR : (⌊x⌋₊ : ℝ)≠0 := by exact_mod_cast hn.ne'
  dsimp
  field_simp

end NField.Alignment.CollisionSpectralMean
