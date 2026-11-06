/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSelectedBox
import NField.Alignment.CommonResetFrequencyPartition

/-! # Exact reconstruction of the original frequency box from its quotient bands -/

noncomputable section

namespace NField.Alignment.CommonResetBoxSource

open scoped BigOperators
open CommonResetSelectedBox CommonResetConductorSelection CommonResetFrequencyPartition
open CommonResetRetainedBands CommonResetNaturalFrequencies

theorem naturalFrequency_eq_zero_above_half {p t u v j : ℕ} (ht : t ≤ p-1) (hu : halfPrime p < u) :
    naturalFrequency p t u v j = 0 := by
  have hcut : ¬ 2*u<t := by have := halfPrime_covers ht; omega
  simp only [naturalFrequency, hcut, false_and, if_false]

theorem boxSlice_full_inverse {p t V J : ℕ} (ht : t ≤ p-1) :
    boxSlice p t V J = ∑ u ∈ Finset.Icc 1 p, ∑ v ∈ Finset.Icc 1 V,
      ∑ j ∈ Finset.Icc 1 J, naturalFrequency p t u v j := by
  unfold boxSlice
  apply Finset.sum_subset
  · intro u hu
    have huI := Finset.mem_Icc.mp hu
    exact Finset.mem_Icc.mpr ⟨huI.1, huI.2.trans ((Nat.div_le_self _ _).trans (Nat.sub_le p 1))⟩
  · intro u hu huNot
    have hup : halfPrime p < u := by
      have huI := Finset.mem_Icc.mp hu
      simp only [Finset.mem_Icc, not_and] at huNot
      exact Nat.lt_of_not_ge (huNot huI.1)
    simp only [naturalFrequency_eq_zero_above_half ht hup, Finset.sum_const_zero]

theorem collapse_quotient_bands {p u v j : ℕ} (hp : 1 ≤ p) (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
      ∑ t ∈ conductorSelection p m u v j K (Finset.Icc 2 (p-1)), originalFrequency p t u v j) =
      ∑ t ∈ Finset.Icc 2 (p-1), if K<t then
        (harmonic ((p-1)/t) : ℝ)*naturalFrequency p t u v j else 0 := by
  simp_rw [conductorSelection, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have htI := Finset.mem_Icc.mp ht
  have hqmem : (p-1)/t ∈ Finset.Icc 1 p := Finset.mem_Icc.mpr
    ⟨Nat.div_pos htI.2 (by omega), (Nat.div_le_self (p-1) t).trans (Nat.sub_le p 1)⟩
  rw [Finset.sum_eq_single_of_mem ((p-1)/t) hqmem]
  · by_cases hKt : K<t <;> by_cases hc : 2*u<t ∧ 2*v<t ∧ 2*j<t <;>
      simp only [hKt, hc, ht, naturalFrequency, and_true, true_and, false_and, and_false, if_true, if_false, mul_zero]
  · intro m hm hmne
    have hne : (p-1)/t ≠ m := Ne.symm hmne
    simp only [hne, false_and, and_false, if_false, mul_zero]

/-- Title: `The actual source box is exactly its complete quotient-band sum`. -/
theorem largeBoxSource_eq_selectedBox {p V J : ℕ} (hp : 1 ≤ p) :
    largeBoxSource p (quarterCutoff p) V J =
      selectedBox p V J (fun _ _ _ _ => Finset.Icc 2 (p-1)) := by
  have hright : selectedBox p V J (fun _ _ _ _ => Finset.Icc 2 (p-1)) =
      ∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, ∑ u ∈ Finset.Icc 1 p,
        ∑ t ∈ Finset.Icc 2 (p-1), if quarterCutoff p<t then
          (harmonic ((p-1)/t) : ℝ)*naturalFrequency p t u v j else 0 := by
    unfold selectedBox
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    simpa only [Finset.mul_sum] using collapse_quotient_bands (u := u) (v := v) (j := j) hp (quarterCutoff p)
  rw [hright]
  unfold largeBoxSource
  have hleft : (∑ t ∈ Finset.Icc 2 (p-1), if quarterCutoff p<t then
      (harmonic ((p-1)/t) : ℝ)*boxSlice p t V J else 0) =
      ∑ t ∈ Finset.Icc 2 (p-1), ∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J,
        ∑ u ∈ Finset.Icc 1 p, if quarterCutoff p<t then
          (harmonic ((p-1)/t) : ℝ)*naturalFrequency p t u v j else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [boxSlice_full_inverse (Finset.mem_Icc.mp ht).2]
    by_cases hKt : quarterCutoff p<t
    · simp only [if_pos hKt]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    · simp only [if_neg hKt, Finset.sum_const_zero]
  rw [hleft, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

/-- Title: `The original unaltered source box obeys the full inverse-frequency estimate`. -/
theorem large_box_source_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p V J : ℕ, p.Prime → V ≤ p → J ≤ p →
      |largeBoxSource p (quarterCutoff p) V J| ≤
        C*(p : ℝ)^(3/2+ε)*(Real.sqrt ((J : ℝ)*V)+1) := by
  obtain ⟨C, hC, hc⟩ := selected_box_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p V J hp hV hJ
  rw [largeBoxSource_eq_selectedBox hp.one_le]
  apply hc p V J hp hV hJ
  intro m u v j i hi k hk t hit htk
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1.trans hit, htk.trans (Finset.mem_Icc.mp hk).2⟩

end NField.Alignment.CommonResetBoxSource
