/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentLocalSeries

/-!
# Local alignment bounds and absent primes
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentLocalBounds

open scoped Classical
open Filter CollisionResetLocalFactors CollisionAlignmentLocalSeries

theorem alignmentPrimeFactor_bounds {p : ℝ} (hp : 1 < p) (v : ℕ) :
    1 ≤ alignmentPrimeFactor p v ∧ alignmentPrimeFactor p v ≤ 1+p⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hpplus : 0 < p+1 := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp.le
  have hv : (p⁻¹)^v ≤ 1 := pow_le_one₀ hr hr1
  have hb : (p⁻¹)^v/(p+1) ≤ p⁻¹ := by
    apply (div_le_iff₀ hpplus).mpr
    rw [mul_add,inv_mul_cancel₀ hp0.ne',mul_one]
    linarith
  constructor
  · unfold alignmentPrimeFactor
    linarith
  · exact sub_le_self _ (div_nonneg (pow_nonneg hr _) hpplus.le)

theorem alignmentPrimeNumerator_gap {p : ℝ} (hp : 1 < p) (v : ℕ) :
    alignmentPrimeFactor p v/(p-1)-alignmentPrimeNumerator p v=
      (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hpplus : p+1 ≠ 0 := ne_of_gt (by linarith)
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hden : 1-(p⁻¹)^2 ≠ 0 := ne_of_gt (by nlinarith)
  rw [alignmentPrimeNumerator_formula hp v,resetPrimeNumerator_formula hp v]
  unfold alignmentPrimeFactor
  have he : 1-(p⁻¹)^2=(p-1)*(p+1)/p^2 := by
    field_simp
    ring
  rw [he]
  simp only [pow_add,pow_one]
  field_simp [hp0.ne',hp1,hpplus]
  ring

theorem alignmentPrimeAverage_bounds {p : ℝ} (hp : 1 < p) (v : ℕ) :
    0 ≤ alignmentPrimeAverage p v ∧ alignmentPrimeAverage p v ≤ 1/(p-1) := by
  have hK : 0 < alignmentPrimeFactor p v :=
    (by norm_num : (0 : ℝ) < 1).trans_le (alignmentPrimeFactor_bounds hp v).1
  have hg := alignmentPrimeNumerator_gap hp v
  have hn : 0 ≤ (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2)) := by
    have hp0 : 0 < p := by linarith
    positivity
  constructor
  · exact div_nonneg (alignmentPrimeNumerator_nonneg hp v) hK.le
  · apply (div_le_iff₀ hK).mpr
    change alignmentPrimeNumerator p v ≤ 1/(p-1)*alignmentPrimeFactor p v
    have he : 1/(p-1)*alignmentPrimeFactor p v=alignmentPrimeFactor p v/(p-1) := by ring
    rw [he]
    linarith

theorem alignmentPrimeFactor_zero {p : ℝ} (hp : 1 < p) :
    alignmentPrimeFactor p 0=1+1/(p*(p+1)) := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hpplus : p+1 ≠ 0 := ne_of_gt (by linarith)
  unfold alignmentPrimeFactor
  simp only [pow_zero]
  field_simp
  ring

theorem alignmentPrimeAverage_zero {p : ℝ} (hp : 1 < p) :
    alignmentPrimeAverage p 0=1/(p^2-1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hpplus : p+1 ≠ 0 := ne_of_gt (by linarith)
  have hpsq : p^2-1 ≠ 0 := ne_of_gt (by nlinarith)
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hden : 1-(p⁻¹)^2 ≠ 0 := ne_of_gt (by nlinarith)
  have hK : alignmentPrimeFactor p 0 ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (alignmentPrimeFactor_bounds hp 0).1)
  unfold alignmentPrimeAverage
  apply (div_eq_iff hK).mpr
  rw [alignmentPrimeNumerator_formula hp 0]
  simp only [resetPrimeNumerator,Finset.range_zero,Finset.sum_empty,Nat.cast_zero,zero_add]
  unfold alignmentPrimeFactor
  simp only [pow_zero]
  field_simp
  ring

theorem alignmentPrimeAverage_zero_bound {p : ℝ} (hp : 2 ≤ p) :
    alignmentPrimeAverage p 0 ≤ 2/p^2 := by
  rw [alignmentPrimeAverage_zero (by linarith)]
  have hp2 : 0 < p^2 := by positivity
  have hden : 0 < p^2-1 := by nlinarith
  apply (div_le_div_iff₀ hden hp2).mpr
  nlinarith

theorem alignment_prime_local_bounds {p : ℝ} (hp : 2 ≤ p) (v : ℕ) :
    alignmentPrimeFactor p v ≤ 1+1/p ∧
      alignmentPrimeAverage p v ≤ 1/(p-1) ∧
      alignmentPrimeFactor p 0=1+1/(p*(p+1)) ∧
      |alignmentPrimeAverage p 0| ≤ 2/p^2 := by
  have hp1 : 1 < p := by linarith
  refine ⟨?_,(alignmentPrimeAverage_bounds hp1 v).2,alignmentPrimeFactor_zero hp1,?_⟩
  · simpa only [one_div] using (alignmentPrimeFactor_bounds hp1 v).2
  · rw [abs_of_nonneg (alignmentPrimeAverage_bounds hp1 0).1]
    exact alignmentPrimeAverage_zero_bound hp

theorem alignmentPrimeFactor_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (alignmentPrimeFactor p) atTop (nhds (1+p⁻¹)) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).div_const (p+1)
  change Tendsto (fun v => 1+p⁻¹-(p⁻¹)^v/(p+1)) atTop (nhds (1+p⁻¹))
  simpa only [zero_div,sub_zero] using h.const_sub (1+p⁻¹)

theorem alignmentPrimeNumerator_gap_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (fun v : ℕ =>
      (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2))) atTop (nhds 0) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hnorm : ‖p⁻¹‖ < 1 := by simpa only [Real.norm_of_nonneg hr] using hr1
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.tendsto_atTop_zero
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he (v : ℕ) : (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2))=
      ((v : ℝ)*(p⁻¹)^v)/(p+1)+(p⁻¹)^v*((p^2+p+1)/((p-1)*(p+1)^2)) := by ring
  simp_rw [he]
  simpa only [zero_div,zero_mul,zero_add] using
    (hn.div_const (p+1)).add (hg.mul_const ((p^2+p+1)/((p-1)*(p+1)^2)))

theorem alignmentPrimeAverage_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (alignmentPrimeAverage p) atTop (nhds (1/(p-1))) := by
  have he (v : ℕ) : alignmentPrimeNumerator p v=alignmentPrimeFactor p v/(p-1)-
      (p⁻¹)^v*((v : ℝ)/(p+1)+(p^2+p+1)/((p-1)*(p+1)^2)) := by
    linarith [alignmentPrimeNumerator_gap hp v]
  have hN : Tendsto (alignmentPrimeNumerator p) atTop (nhds ((1+p⁻¹)/(p-1))) := by
    change Tendsto (fun v => alignmentPrimeNumerator p v) atTop (nhds ((1+p⁻¹)/(p-1)))
    simp_rw [he]
    simpa only [sub_zero] using
      ((alignmentPrimeFactor_tendsto hp).div_const (p-1)).sub (alignmentPrimeNumerator_gap_tendsto hp)
  have hp0 : 0 < p := by linarith
  have hK : 1+p⁻¹ ≠ 0 := ne_of_gt (by positivity)
  have h : Tendsto (fun v => alignmentPrimeNumerator p v/alignmentPrimeFactor p v)
      atTop (nhds (((1+p⁻¹)/(p-1))/(1+p⁻¹))) :=
    hN.div (alignmentPrimeFactor_tendsto hp) hK
  have hc : ((1+p⁻¹)/(p-1))/(1+p⁻¹)=1/(p-1) := by field_simp
  change Tendsto (fun v => alignmentPrimeNumerator p v/alignmentPrimeFactor p v)
    atTop (nhds (1/(p-1)))
  simpa only [hc] using h

end NField.Alignment.CollisionAlignmentLocalBounds
