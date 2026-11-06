/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetPrintedScales
import NField.Alignment.CommonResetSmallSource
import NField.Alignment.CommonResetDivisorSums
import NField.Alignment.CommonResetTwistMass

/-! # Literal intermediate display bounds and real cutoffs -/

noncomputable section

namespace NField.Alignment.CommonResetDisplayBounds

open scoped BigOperators
open Set CommonResetDerivativeSmooth CommonResetDerivativeIntervals CommonResetTwistMass
open CommonResetDivisorSums CommonResetRootSums CommonResetSmallSource
open CommonResetConductorSelection CommonResetFrequencyPartition CommonResetBoxSummation
open CommonResetSmallConductors CommonResetGeometricMass
open DedekindInverseResidueTransform

theorem sampled_derivative_interval (g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    lam*N ≤ g (a+N)-g a ∧ g (a+N)-g a ≤ A*lam*N ∧ A*lam*N ≤ A*lam*(N+1) := by
  have he := derivative_variation g k hg hgk hk
    (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem (le_refl N)) (by simp)
  simp only [Nat.cast_zero, add_zero, add_sub_cancel_left] at he
  exact ⟨he.1, he.2, by nlinarith [mul_pos (by linarith : 0 < A) hlam]⟩

/-- Title: `The near-slope inverse-curvature contribution has exactly the displayed upper bound`. -/
theorem near_inverse_curvature {u L δ A lam : ℝ} (hu : 0 ≤ u) (hlam : 0 < lam)
    (hδ : δ ≤ A*lam*L) :
    (u*δ+4)/Real.sqrt lam ≤ A*u*L*Real.sqrt lam+4/Real.sqrt lam := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have he := Real.sq_sqrt hlam.le
  calc
    _ ≤ (u*(A*lam*L)+4)/Real.sqrt lam :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hδ hu) (le_refl 4)) hs.le
    _ = _ := by
      field_simp [hs.ne']
      linear_combination -(A*u*L)*he

/-- Title: `The small-conductor source has the literal three-logarithm bound`. -/
theorem small_source_log_bound {p : ℕ} (hp : p.Prime) :
    |smallSource p (quarterCutoff p)| ≤ 8*(p : ℝ)^(3/2 : ℝ)*(Real.log (2*(p : ℝ)))^3 := by
  have hp1 := hp.one_le
  have hH := harmonic_nonneg p
  have hlog : 0 ≤ Real.log (2*(p : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*p by omega))
  calc
    _ ≤ (harmonic p : ℝ)^3*(p : ℝ)^(3/2 : ℝ) := small_source_finite_bound hp
    _ ≤ (2*Real.log (2*(p : ℝ)))^3*(p : ℝ)^(3/2 : ℝ) := by
      gcongr
      exact harmonic_le_twice_log hp.pos
    _ = _ := by ring

/-- Title: `Both inverse-frequency divisor bounds hold with the manuscript's real upper cutoff`. -/
theorem gcd_sums_real_cutoff {a : ℕ} (ha : 0 < a) {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ u ∈ Finset.Icc 1 ⌊Y⌋₊, Real.sqrt (a.gcd u : ℝ)/(u : ℝ)) ≤
      (harmonic ⌊Y⌋₊ : ℝ)*reciprocalSqrtDivisorSum a ∧
    (∑ u ∈ Finset.Icc 1 ⌊Y⌋₊, Real.sqrt (a.gcd u : ℝ)/Real.sqrt (u : ℝ)) ≤
      2*Real.sqrt Y*reciprocalSqrtDivisorSum a := by
  refine ⟨gcd_harmonic_sum ha _, (gcd_root_sum ha _).trans ?_⟩
  have hd : 0 ≤ reciprocalSqrtDivisorSum a := by
    unfold reciprocalSqrtDivisorSum
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le (by linarith))) (by norm_num)) hd

def harmonicLiftFive (n : ℕ) : ℝ := (harmonic n : ℝ)/((n : ℝ)^2*Real.sqrt (n : ℝ))

/-- Title: `Both harmonic lift series in the full box estimate converge`. -/
theorem both_harmonic_lifts_summable : Summable harmonicLift ∧ Summable harmonicLiftFive := by
  refine ⟨harmonicLift_summable, harmonicLift_summable.of_nonneg_of_le ?_ ?_⟩
  · intro n
    unfold harmonicLiftFive
    have hh := harmonic_nonneg n
    positivity
  · intro n
    by_cases hn : n=0
    · subst n
      simp [harmonicLiftFive, harmonicLift]
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
      unfold harmonicLiftFive harmonicLift
      apply div_le_div_of_nonneg_left (harmonic_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (by nlinarith) hs.le

/-- Title: `The last harmonic band sum has the literal squared-logarithm cost`. -/
theorem harmonic_band_log_cost {p : ℕ} (hp : 0 < p) :
    (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)/(m : ℝ)) ≤
      4*(Real.log (2*(p : ℝ)))^2 := by
  have hH := harmonic_nonneg p
  calc
    _ ≤ (harmonic p : ℝ)^2 := harmonic_weighted_reciprocal p
    _ ≤ (2*Real.log (2*(p : ℝ)))^2 := by
      gcongr
      exact harmonic_le_twice_log hp
    _ = _ := by ring

end NField.Alignment.CommonResetDisplayBounds
