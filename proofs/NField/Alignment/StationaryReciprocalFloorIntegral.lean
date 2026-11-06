/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryTailFunctional

/-! # Exact integration of the reciprocal floor by its finitely many thresholds -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryReciprocalFloorIntegral
open scoped BigOperators
open MeasureTheory Set

theorem reciprocal_threshold {M n j : ℕ} (hM : 0 < M)
    (hj : j ∈ Finset.Icc 1 (n / M)) : (n : ℝ) / j ∈ Icc (M : ℝ) n := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hMj : M * j ≤ n := by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hM).mp (Finset.mem_Icc.mp hj).2
  constructor
  · exact (le_div_iff₀ hj0).mpr (by exact_mod_cast hMj)
  · exact div_le_self (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp hj).1)

theorem reciprocal_floor_count (v : ℝ) {M n : ℕ} (hM : 0 < M)
    {t : ℝ} (ht : t ∈ Icc (M : ℝ) n) :
    v * (⌊(n : ℝ) / t⌋₊ : ℝ) =
      ∑ j ∈ Finset.Icc 1 (n / M), if t ≤ (n : ℝ) / j then v else 0 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have ht0 : 0 < t := hMR.trans_le ht.1
  have hfloor : ⌊(n : ℝ) / t⌋₊ ≤ n / M := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_left (by positivity) hMR ht.1)
  have he : (Finset.Icc 1 (n / M)).filter (fun j : ℕ => t ≤ (n : ℝ) / j) =
      Finset.Icc 1 ⌊(n : ℝ) / t⌋₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj, _⟩, htj⟩
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj
      refine ⟨hj, (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (n : ℝ) / t)).mpr ?_⟩
      apply (le_div_iff₀ ht0).mpr
      simpa only [mul_comm] using (le_div_iff₀ hjR).mp htj
    · rintro ⟨hj, hjf⟩
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj
      refine ⟨⟨hj, hjf.trans hfloor⟩, (le_div_iff₀ hjR).mpr ?_⟩
      have hjt := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (n : ℝ) / t)).mp hjf
      simpa only [mul_comm] using (le_div_iff₀ ht0).mp hjt
  rw [← Finset.sum_filter, he]
  simp [mul_comm]

theorem interval_indicator_integrable {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => if t ≤ c then f t else 0) volume a b := by
  exact intervalIntegrable_iff.mpr (hf.def'.indicator measurableSet_Iic)

theorem reciprocal_floor_integrable {f : ℝ → ℝ} {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n)
    (hf : IntervalIntegrable f volume (M : ℝ) n) :
    IntervalIntegrable (fun t => f t * (⌊(n : ℝ) / t⌋₊ : ℝ)) volume (M : ℝ) n := by
  have hh : IntervalIntegrable (fun t => ∑ j ∈ Finset.Icc 1 (n / M),
      if t ≤ (n : ℝ) / j then f t else 0) volume (M : ℝ) n := by
    convert! IntervalIntegrable.sum (Finset.Icc 1 (n / M))
      (fun j hj => interval_indicator_integrable (c := (n : ℝ) / j) hf) using 1
    funext t
    simp only [Finset.sum_apply]
  apply hh.congr
  intro t ht
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  rw [uIoc_of_le hMnR] at ht
  exact (reciprocal_floor_count (f t) hM ⟨ht.1.le, ht.2⟩).symm

/-- Title: `The reciprocal-floor integral is exactly the sum of its threshold integrals`. -/
theorem reciprocal_floor_integral {f : ℝ → ℝ} {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n)
    (hf : IntervalIntegrable f volume (M : ℝ) n) :
    (∫ t in (M : ℝ)..n, f t * (⌊(n : ℝ) / t⌋₊ : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (n / M), ∫ t in (M : ℝ)..((n : ℝ) / j), f t := by
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  calc
    _ = ∫ t in (M : ℝ)..n,
        ∑ j ∈ Finset.Icc 1 (n / M), if t ≤ (n : ℝ) / j then f t else 0 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hMnR] at ht
      exact reciprocal_floor_count (f t) hM ht
    _ = ∑ j ∈ Finset.Icc 1 (n / M), ∫ t in (M : ℝ)..n,
        if t ≤ (n : ℝ) / j then f t else 0 := by
      apply intervalIntegral.integral_finsetSum
      intro j hj
      exact interval_indicator_integrable hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact intervalIntegral.integral_indicator (reciprocal_threshold hM hj)

/-- Title: `The smooth reciprocal-floor integral retains every boundary value`. -/
theorem derivative_reciprocal_floor_integral {F F' : ℝ → ℝ} {M n : ℕ}
    (hM : 0 < M) (hMn : M ≤ n)
    (hd : ∀ t ∈ Icc (M : ℝ) n, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Icc (M : ℝ) n)) :
    (∫ t in (M : ℝ)..n, F' t * (⌊(n : ℝ) / t⌋₊ : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (n / M), (F ((n : ℝ) / j) - F M) := by
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hi : IntervalIntegrable F' volume (M : ℝ) n := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hMnR]
  rw [reciprocal_floor_integral hM hMn hi]
  apply Finset.sum_congr rfl
  intro j hj
  have ht := reciprocal_threshold hM hj
  have hsub : uIcc (M : ℝ) ((n : ℝ) / j) ⊆ Icc (M : ℝ) n := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (hsub ht)) (hc.mono hsub).intervalIntegrable

end NField.Alignment.StationaryReciprocalFloorIntegral
