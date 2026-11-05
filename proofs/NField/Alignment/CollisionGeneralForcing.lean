/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionL1Testing

/-!
# The L1 divisor forcing of a general positive mass

The reset series is constructed in Haar L1. Lowering the finite Hilbert
differences gives this same series, with the finite mass retained until
the unit-mass limit has been justified.
-/

noncomputable section

namespace NField.Alignment.CollisionGeneralForcing

open scoped BigOperators ENNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialCoboundary CollisionResetIntegrability CollisionL1Testing
open CollisionRemainderDynamics CollisionMassReadout

def generalResetTerm (v : ℕ → ℝ) (k : ℕ) : Phase → ℝ :=
  (resetSet k).indicator (fun _ => (k : ℝ) * v k)

def generalResetL1 (v : ℕ → ℝ) (k : ℕ) : HaarL1 :=
  indicatorConstLp 1 (resetSet_measurable k) (measure_ne_top phaseHaar _) ((k : ℝ)*v k)

theorem generalResetL1_coe (v : ℕ → ℝ) (k : ℕ) :
    (fun x => generalResetL1 v k x) =ᵐ[phaseHaar] generalResetTerm v k :=
  indicatorConstLp_coeFn

theorem generalResetL1_zero (v : ℕ → ℝ) : generalResetL1 v 0 = 0 := by
  apply Lp.ext
  filter_upwards [generalResetL1_coe v 0, Lp.coeFn_zero ℝ 1 phaseHaar] with x hx hz
  rw [hx, hz]
  simp [generalResetTerm]

theorem generalResetL1_one (v : ℕ → ℝ) (h1 : v 1 = 0) : generalResetL1 v 1 = 0 := by
  apply Lp.ext
  filter_upwards [generalResetL1_coe v 1, Lp.coeFn_zero ℝ 1 phaseHaar] with x hx hz
  rw [hx, hz]
  simp [generalResetTerm, h1]

theorem generalResetL1_norm (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (h0 : v 0 = 0) (k : ℕ) :
    ‖generalResetL1 v k‖ = v k := by
  by_cases hk : k = 0
  · simp [hk, generalResetL1_zero, h0]
  rw [generalResetL1, norm_indicatorConstLp (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞), resetSet_measure_real (Nat.pos_of_ne_zero hk)]
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (hv k))]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

theorem generalResetL1_norm_summable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (hs : Summable v) : Summable (fun k => ‖generalResetL1 v k‖) := by
  simpa only [generalResetL1_norm v hv h0] using hs

theorem generalResetL1_tsum_coe (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (hs : Summable v) :
    (fun x => (∑' k, generalResetL1 v k) x) =ᵐ[phaseHaar]
      (fun x => ∑' k, generalResetTerm v k x) := by
  have he : (∑' k, ‖generalResetL1 v k‖ₑ) ≠ ∞ := by
    simpa only [ofReal_norm] using (generalResetL1_norm_summable v hv h0 hs).tsum_ofReal_ne_top
  have ht : ∀ᵐ x ∂phaseHaar, ∀ k, generalResetL1 v k x = generalResetTerm v k x :=
    ae_all_iff.mpr (generalResetL1_coe v)
  filter_upwards [Lp.coeFn_tsum he, ht] with x hx hterms
  exact hx.trans (tsum_congr hterms)

def forcingL1 (v : ℕ → ℝ) : HaarL1 :=
  (2/3 : ℝ) • (lowerL2 oneVector - ∑' k, generalResetL1 v k)

def forcingFunction (v : ℕ → ℝ) (x : Phase) : ℝ :=
  (2/3 : ℝ) * (1 - ∑' k, generalResetTerm v k x)

theorem forcingL1_coe (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (hs : Summable v) :
    (fun x => forcingL1 v x) =ᵐ[phaseHaar] forcingFunction v := by
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  filter_upwards [Lp.coeFn_smul (2/3 : ℝ) (lowerL2 oneVector - ∑' k, generalResetL1 v k),
    Lp.coeFn_sub (lowerL2 oneVector) (∑' k, generalResetL1 v k),
    generalResetL1_tsum_coe v hv h0 hs, ho] with x hsm hsub ht hox
  change oneVector x = 1 at hox
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lowerL2_coe] at hsm hsub
  change ((2/3 : ℝ) • (lowerL2 oneVector - ∑' k, generalResetL1 v k)) x = _
  rw [hsm, hsub, hox, ht]
  rfl

theorem forcingFunction_integrable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (hs : Summable v) : Integrable (forcingFunction v) phaseHaar := by
  exact memLp_one_iff_integrable.mp
    (MemLp.ae_eq (forcingL1_coe v hv h0 hs) (Lp.memLp (forcingL1 v)))

theorem general_weighted_step (v : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    lowerL2 (v k • (remainderVector k - shift (-1) (remainderVector k))) =
      v k • lowerL2 oneVector - generalResetL1 v k := by
  apply Lp.ext
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (remainderMap k)
  have ht := (translate_measurePreserving (-1)).quasiMeasurePreserving.ae
    (p := fun x => remainderVector k x = centered k x) hr
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  filter_upwards [Lp.coeFn_smul (v k) (remainderVector k - shift (-1) (remainderVector k)),
    Lp.coeFn_sub (remainderVector k) (shift (-1) (remainderVector k)),
    shift_coe (-1) (remainderVector k), hr, ht, ho,
    Lp.coeFn_sub (v k • lowerL2 oneVector) (generalResetL1 v k),
    Lp.coeFn_smul (v k) (lowerL2 oneVector), generalResetL1_coe v k]
    with x hsm hsub hsh hrx htx hox hsub1 hsm1 hreset
  change remainderVector k x = centered k x at hrx
  change oneVector x = 1 at hox
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lowerL2_coe] at hsm hsub hsub1 hsm1
  rw [lowerL2_coe, hsm, hsub, hsh, hrx, htx, hsub1, hsm1, hox, hreset,
    centered_backward_step hk]
  unfold generalResetTerm
  by_cases hx : x ∈ resetSet k
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    ring

def finiteForcing (v : ℕ → ℝ) (M : ℕ) : HaarL1 :=
  (2/3 : ℝ) • ((∑ k ∈ Finset.Icc 2 M, v k) • lowerL2 oneVector -
    ∑ k ∈ Finset.Icc 2 M, generalResetL1 v k)

theorem finiteForcing_eq_lower_difference (v : ℕ → ℝ) (M : ℕ) :
    finiteForcing v M = lowerL2 (finitePotential v M - shift (-1) (finitePotential v M)) := by
  symm
  simp only [finitePotential, map_smul, map_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  unfold finiteForcing
  congr 1
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [map_smul] using general_weighted_step v (by have := (Finset.mem_Icc.mp hk).1; omega)

theorem generalResetL1_partial_tendsto (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) :
    Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, generalResetL1 v k) atTop
      (nhds (∑' k, generalResetL1 v k)) := by
  have he (M : ℕ) : (∑ k ∈ Finset.range (M+1), generalResetL1 v k) =
      ∑ k ∈ Finset.Icc 2 M, generalResetL1 v k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hn
      have hkn := Finset.mem_range.mp hk
      have hk2 : k < 2 := by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega
      interval_cases k <;> simp [generalResetL1_zero, generalResetL1_one v h1]
  simpa only [Function.comp_def, he] using
    (generalResetL1_norm_summable v hv h0 hs).of_norm.hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)

theorem finiteForcing_tendsto (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : HasSum v 1) :
    Tendsto (finiteForcing v) atTop (nhds (forcingL1 v)) := by
  have hm : Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, v k) atTop (nhds 1) := by
    simpa only [Function.comp_def, sum_range_zero_one v h0 h1] using
      hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h := ((hm.smul_const (lowerL2 oneVector)).sub
    (generalResetL1_partial_tendsto v hv h0 h1 hs.summable)).const_smul (2/3 : ℝ)
  unfold finiteForcing forcingL1
  simpa only [one_smul] using h

end NField.Alignment.CollisionGeneralForcing
