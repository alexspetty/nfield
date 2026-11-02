/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMertensInput
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact finite prime-power reset factors

The finite exponent is retained throughout. These factors are the
literal A_p(v) and numerator of t_p(v) in the maximal-order proof.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResetLocalFactors

open scoped Classical
open Filter

def resetPrimeFactor (p : ℝ) (v : ℕ) : ℝ := 1+p⁻¹-(p⁻¹)^(v+1)

def resetPrimeNumerator (p : ℝ) (v : ℕ) : ℝ :=
  ∑ j ∈ Finset.range v, (1-p⁻¹)*(p⁻¹)^(j+1)*((j : ℝ)+1+(p-1)⁻¹)

def resetPrimeAverage (p : ℝ) (v : ℕ) : ℝ := resetPrimeNumerator p v/resetPrimeFactor p v

theorem resetPrimeFactor_succ (p : ℝ) (v : ℕ) :
    resetPrimeFactor p (v+1)=resetPrimeFactor p v+(1-p⁻¹)*(p⁻¹)^(v+1) := by
  unfold resetPrimeFactor
  rw [pow_succ (p⁻¹) (v+1)]
  ring

theorem resetPrimeNumerator_succ (p : ℝ) (v : ℕ) :
    resetPrimeNumerator p (v+1)=resetPrimeNumerator p v+
      (1-p⁻¹)*(p⁻¹)^(v+1)*((v : ℝ)+1+(p-1)⁻¹) := by
  simp only [resetPrimeNumerator,Finset.sum_range_succ]

theorem resetPrimeFactor_bounds {p : ℝ} (hp : 1 < p) (v : ℕ) :
    1 ≤ resetPrimeFactor p v ∧ resetPrimeFactor p v ≤ 1+p⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp.le
  have hv : (p⁻¹)^v ≤ 1 := pow_le_one₀ hr hr1
  have hpow : (p⁻¹)^(v+1) ≤ p⁻¹ := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hv hr
  constructor
  · dsimp [resetPrimeFactor]
    linarith
  · exact sub_le_self _ (pow_nonneg hr _)

theorem resetPrimeNumerator_nonneg {p : ℝ} (hp : 1 < p) (v : ℕ) :
    0 ≤ resetPrimeNumerator p v := by
  have hp0 : 0 < p := by linarith
  have hr1 : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp.le
  unfold resetPrimeNumerator
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) (by positivity)) (by positivity)

theorem resetPrimeNumerator_gap {p : ℝ} (hp : 1 < p) (v : ℕ) :
    resetPrimeFactor p v/(p-1)-resetPrimeNumerator p v=
      (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹) := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hc : (p-1)⁻¹*(1-p⁻¹)=p⁻¹ := by
    field_simp
  induction v with
  | zero => simp [resetPrimeFactor,resetPrimeNumerator]
  | succ v ih =>
    rw [resetPrimeFactor_succ,resetPrimeNumerator_succ]
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      _ = (resetPrimeFactor p v/(p-1)-resetPrimeNumerator p v)-
          ((v : ℝ)+1)*(1-p⁻¹)*(p⁻¹)^(v+1) := by ring
      _ = (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹)-
          ((v : ℝ)+1)*(1-p⁻¹)*(p⁻¹)^(v+1) := by rw [ih]
      _ = _ := by
        rw [pow_succ]
        linear_combination (p⁻¹)^v*hc

theorem resetPrimeAverage_bounds {p : ℝ} (hp : 1 < p) (v : ℕ) :
    0 ≤ resetPrimeAverage p v ∧ resetPrimeAverage p v ≤ 1/(p-1) := by
  have hA : 0 < resetPrimeFactor p v := (by norm_num : (0 : ℝ) < 1).trans_le (resetPrimeFactor_bounds hp v).1
  have hg := resetPrimeNumerator_gap hp v
  have hn : 0 ≤ (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹) := by
    have hp0 : 0 < p := by linarith
    positivity
  constructor
  · exact div_nonneg (resetPrimeNumerator_nonneg hp v) hA.le
  · apply (div_le_iff₀ hA).mpr
    change resetPrimeNumerator p v ≤ 1/(p-1)*resetPrimeFactor p v
    have he : 1/(p-1)*resetPrimeFactor p v=resetPrimeFactor p v/(p-1) := by ring
    rw [he]
    linarith

theorem resetPrimeNumerator_formula {p : ℝ} (hp : 1 < p) (v : ℕ) :
    resetPrimeNumerator p v=
      (1+p⁻¹-((v : ℝ)+1)*(p⁻¹)^v+((v : ℝ)-1)*(p⁻¹)^(v+1))/(p-1) := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  calc
    _ = resetPrimeFactor p v/(p-1)-(p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹) := by
      linarith [resetPrimeNumerator_gap hp v]
    _ = _ := by
      unfold resetPrimeFactor
      rw [pow_succ]
      field_simp
      ring

theorem resetPrimeNumerator_Icc (p : ℝ) (v : ℕ) :
    resetPrimeNumerator p v=
      ∑ j ∈ Finset.Icc 1 v, (1-1/p)/p^j*((j : ℝ)+1/(p-1)) := by
  let F : ℕ → ℝ := fun j => (1-1/p)/p^j*((j : ℝ)+1/(p-1))
  calc
    _ = ∑ j ∈ Finset.range v, F (j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [F,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,inv_pow,one_mul]
    _ = _ := by
      simpa only [Nat.zero_add,Finset.range_eq_Ico,Finset.Ico_add_one_right_eq_Icc] using
        (Finset.sum_Ico_add' F 0 v 1)

theorem reset_prime_local_factors (p : ℝ) (v : ℕ) :
    resetPrimeFactor p v=1+1/p-1/p^(v+1) ∧
      resetPrimeAverage p v=
        (∑ j ∈ Finset.Icc 1 v, (1-1/p)/p^j*((j : ℝ)+1/(p-1)))/resetPrimeFactor p v := by
  constructor
  · simp only [resetPrimeFactor,one_div,inv_pow]
  · rw [resetPrimeAverage,resetPrimeNumerator_Icc]

theorem resetPrimeFactor_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (resetPrimeFactor p) atTop (nhds (1+p⁻¹)) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun v => 1+p⁻¹-(p⁻¹)^(v+1)) atTop (nhds (1+p⁻¹))
  simpa only [resetPrimeFactor,Function.comp_def,sub_zero] using h.const_sub (1+p⁻¹)

theorem resetPrimeNumerator_gap_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (fun v : ℕ => (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹)) atTop (nhds 0) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hnorm : ‖p⁻¹‖ < 1 := by simpa only [Real.norm_of_nonneg hr] using hr1
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.tendsto_atTop_zero
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he (v : ℕ) : (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹)=
      ((v : ℝ)*(p⁻¹)^v)*p⁻¹+(p⁻¹)^v*(p-1)⁻¹ := by ring
  simp_rw [he]
  simpa only [zero_mul,zero_add] using (hn.mul_const p⁻¹).add (hg.mul_const (p-1)⁻¹)

theorem resetPrimeAverage_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (resetPrimeAverage p) atTop (nhds (1/(p-1))) := by
  have he (v : ℕ) : resetPrimeNumerator p v=resetPrimeFactor p v/(p-1)-
      (p⁻¹)^v*((v : ℝ)*p⁻¹+(p-1)⁻¹) := by linarith [resetPrimeNumerator_gap hp v]
  have hN : Tendsto (resetPrimeNumerator p) atTop (nhds ((1+p⁻¹)/(p-1))) := by
    change Tendsto (fun v => resetPrimeNumerator p v) atTop (nhds ((1+p⁻¹)/(p-1)))
    simp_rw [he]
    simpa only [sub_zero] using
      ((resetPrimeFactor_tendsto hp).div_const (p-1)).sub (resetPrimeNumerator_gap_tendsto hp)
  have hp0 : 0 < p := by linarith
  have hA : 1+p⁻¹ ≠ 0 := ne_of_gt (by positivity)
  have h : Tendsto (fun v => resetPrimeNumerator p v/resetPrimeFactor p v)
      atTop (nhds (((1+p⁻¹)/(p-1))/(1+p⁻¹))) :=
    hN.div (resetPrimeFactor_tendsto hp) hA
  have hc : ((1+p⁻¹)/(p-1))/(1+p⁻¹)=1/(p-1) := by field_simp
  change Tendsto (fun v => resetPrimeNumerator p v/resetPrimeFactor p v)
    atTop (nhds (1/(p-1)))
  simpa only [hc] using h

end NField.Alignment.CollisionResetLocalFactors
