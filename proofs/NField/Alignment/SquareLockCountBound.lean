/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SquareLockCountScales
import NField.Alignment.SquareLockResidueArc
import NField.Alignment.ReciprocalDyadicPartition

/-! # The actual square-lock carrier count at its printed scale -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockCountBound
open scoped BigOperators Classical
open SquareLockCountScales SquareLockResidueArc SquareLockCarrierMass
  ReciprocalArcBlock ReciprocalDyadicPartition

def selectedIndicator (p C n : ℕ) : ℝ :=
  if n ∈ smallDisplacementCarriers p C then 1 else 0

theorem selected_count_prefix (p C : ℕ) :
    ((smallDisplacementCarriers p C).card:ℝ) =
      prefixSum (selectedIndicator p C) (p-1) := by
  have he : prefixSum (selectedIndicator p C) (p-1) =
      ∑ n ∈ Finset.Icc 1 (p-1), selectedIndicator p C n := by
    unfold prefixSum
    apply Finset.sum_bij (fun i _ => i+1)
    · intro i hi
      have := Finset.mem_range.mp hi
      simp only [Finset.mem_Icc]
      omega
    · intro i hi j hj he; omega
    · intro n hn
      have := Finset.mem_Icc.mp hn
      exact ⟨n-1,Finset.mem_range.mpr (by omega),by omega⟩
    · intro i hi; rfl
  rw [he]
  unfold selectedIndicator
  rw [← Finset.sum_filter]
  have hf : (Finset.Icc 1 (p-1)).filter (fun n => n ∈ smallDisplacementCarriers p C) =
      smallDisplacementCarriers p C := by
    ext n
    simp only [Finset.mem_filter,smallDisplacementCarriers,Finset.mem_Icc]
    omega
  rw [hf]
  simp

theorem selected_initial_bound (p C : ℕ) :
    prefixSum (selectedIndicator p C) (min (p-1) 4) ≤ 4 := by
  unfold prefixSum
  calc
    _ ≤ ∑ _i ∈ Finset.range (min (p-1) 4), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold selectedIndicator
      split_ifs <;> norm_num
    _ ≤ _ := by simp

theorem selected_block_bound (p C j : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.range (length (p-1) j), selectedIndicator p C (start j+i+1)) ≤
      1160*countScale (p:ℝ) C := by
  let P := start j
  let M := length (p-1) j
  let s := (Finset.range M).filter (fun i => start j+i+1 ∈ smallDisplacementCarriers p C)
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  obtain ⟨hT,hCT,hpow⟩ := countScale_bounds (p:ℝ) C hp1 (Nat.cast_nonneg C)
  by_cases hz : M = 0
  · change (∑ i ∈ Finset.range M, _) ≤ _
    rw [hz]
    simp only [Finset.range_zero,Finset.sum_empty]
    positivity
  have hPp : P < p := by
    dsimp [M,length] at hz
    dsimp [P]
    omega
  have hP : 1 ≤ P := by
    dsimp [P,start]
    have hp2 : 0 < (2:ℕ)^j := by positivity
    omega
  have hM : M ≤ P := length_le_start (p-1) j
  have hs : s ⊆ Finset.range M := Finset.filter_subset _ _
  have harc (i : ℕ) (hi : i ∈ s) :
      ∃ z : ℤ, |(p:ℝ)^2/((P+i+1:ℕ):ℝ)-z| ≤ (C:ℝ)/(P:ℝ) := by
    have hmem := (Finset.mem_filter.mp hi).2
    have hc := (Finset.mem_filter.mp hmem).2.2
    have hk : 0 < P+i+1 := by omega
    obtain ⟨z,hz⟩ := centered_residue_small_arc (p^2) (P+i+1) C hk hc
    refine ⟨z,?_⟩
    have hPc : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    calc
      _ ≤ (C:ℝ)/((P+i+1:ℕ):ℝ) := by simpa only [Nat.cast_pow] using hz
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg C) hPc
        (by exact_mod_cast (show P ≤ P+i+1 by omega))
  have hb := reciprocal_arc_block P M p C (countScale (p:ℝ) C) s hP hM
    (by exact_mod_cast hPp.le) (Nat.cast_nonneg C) hCT hT hpow
    (block_log_scale P p C hP (by exact_mod_cast hPp.le) (Nat.cast_nonneg C)) hs harc
  have he : (∑ i ∈ Finset.range M, selectedIndicator p C (start j+i+1)) = (s.card:ℝ) := by
    simp only [selectedIndicator,← Finset.sum_filter]
    simp [s]
  change (∑ i ∈ Finset.range M, _) ≤ _
  rw [he]
  exact hb

theorem square_lock_count_bound (p C : ℕ) (hp : 2 ≤ p) (hC : 1 ≤ C) :
    ((smallDisplacementCarriers p C).card:ℝ) ≤
      2400*((C:ℝ)*Real.log (2*p)+Real.rpow p (2/3:ℝ)*Real.log (2*p)) := by
  let T := countScale (p:ℝ) C
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  obtain ⟨hT,hCT,hpow⟩ := countScale_bounds (p:ℝ) C hp1 (Nat.cast_nonneg C)
  have hT1 : 1 ≤ T := (by exact_mod_cast hC : (1:ℝ) ≤ C).trans hCT
  have hL : (1/2:ℝ) ≤ Real.log (2*p) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hJ := dyadic_count_log_bound (p-1) p (by omega) (by exact_mod_cast Nat.sub_le p 1)
  have hb : ((smallDisplacementCarriers p C).card:ℝ) ≤
      4+(Nat.log 2 (p-1):ℝ)*(1160*T) := by
    rw [selected_count_prefix,full_prefix_partition _ (p-1) (Nat.log 2 (p-1))
      (logarithmic_cover (p-1))]
    apply add_le_add (selected_initial_bound p C)
    calc
      _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 (p-1)), 1160*T := by
        apply Finset.sum_le_sum
        intro j hj
        exact selected_block_bound p C j hp
      _ = _ := by simp
  have hTL : (1/2:ℝ) ≤ T*Real.log (2*p) := by
    nlinarith [mul_le_mul_of_nonneg_right hT1 (show 0 ≤ Real.log (2*p) by linarith)]
  calc
    _ ≤ 4+(Nat.log 2 (p-1):ℝ)*(1160*T) := hb
    _ ≤ 4+(2*Real.log (2*p))*(1160*T) := by gcongr
    _ ≤ 2400*(T*Real.log (2*p)) := by nlinarith
    _ = _ := by dsimp [T,countScale]; ring

/-- Title: `Square-lock carrier count`. -/
theorem square_lock_count_estimate : SquareLockCountEstimate := by
  refine ⟨2400,by norm_num,?_⟩
  intro p C hp hC hhalf
  exact square_lock_count_bound p C hp.two_le hC

end NField.Alignment.SquareLockCountBound
