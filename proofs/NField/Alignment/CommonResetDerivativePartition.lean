/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDerivativeIntervals

/-! # Partitioning an actual phase by its monotone derivative -/

noncomputable section

namespace NField.Alignment.CommonResetDerivativePartition

open scoped BigOperators
open Set CommonResetDerivativeFirst CommonResetDerivativeSmooth
open CommonResetDerivativeIntervals CommonResetIntegerCounts

theorem sampled_derivative_separation (g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam upper : ℝ} (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ upper)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    lam*((j : ℝ)-i) ≤ g (a+j)-g (a+i) := by
  have hv := (derivative_variation g k hg hgk hk (natural_sample_mem (hij.trans hj))
    (natural_sample_mem hj) (by exact_mod_cast (show a+(i : ℝ) ≤ a+j from by gcongr))).1
  simpa only [add_sub_add_left_eq_sub] using hv

theorem derivative_strip_count (g : ℝ → ℝ) (a : ℝ) (N : ℕ) (d B : ℝ)
    (hg : MonotoneOn g (Icc a (a+N))) (hvar : g (a+N)-g a ≤ B) :
    (((Finset.range (N+1)).image (fun i : ℕ => ⌊g (a+i)+d⌋)).card : ℝ) ≤ B+2 := by
  classical
  let T := (Finset.range (N+1)).image (fun i : ℕ => ⌊g (a+i)+d⌋)
  have hB : 0 ≤ B := by
    have hm := hg (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem (le_refl N))
      (by simp)
    simp only [Nat.cast_zero, add_zero] at hm
    linarith
  have hbound : ∀ z ∈ T, g a+d-1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ g (a+N)+d := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
    have hlo := hg (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem hiN) (by simp)
    have hhi := hg (natural_sample_mem hiN) (natural_sample_mem (le_refl N)) (by gcongr)
    simp only [Nat.cast_zero, add_zero] at hlo
    constructor
    · linarith [Int.lt_floor_add_one (g (a+i)+d)]
    · linarith [Int.floor_le (g (a+i)+d)]
  have hc := integer_card_bound T hbound
  have hb : max 0 (g (a+N)+d-(g a+d-1)+1) ≤ B+2 := by
    apply max_le <;> linarith
  exact hc.trans hb

/-- Title: `The second-derivative estimate follows from the actual near and far slope partition`. -/
theorem second_derivative_split_bound (f g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam A d : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A) (hd : 0 < d) (hdh : d ≤ 1/2)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    ‖∑ i ∈ Finset.range (N+1), phase (f (a+i))‖ ≤
      (A*lam*N+2)*(2*d/lam+1+2/d) := by
  classical
  let S := Finset.range (N+1)
  let label (i : ℕ) : ℤ := ⌊g (a+i)+d⌋
  let T := S.image label
  have hmono := derivative_monotone_of_curvature g k hlam.le hg hgk hk
  have hvar : g (a+N)-g a ≤ A*lam*N := by
    have hv := (derivative_variation g k hg hgk hk
      (natural_sample_mem (Nat.zero_le N)) (natural_sample_mem (le_refl N)) (by simp)).2
    simpa using hv
  have hcount : (T.card : ℝ) ≤ A*lam*N+2 := derivative_strip_count g a N d _ hmono hvar
  have hcost : 0 ≤ 2*d/lam+1+2/d := by positivity
  have hfiber (m : ℤ) :
      ‖∑ i ∈ S.filter (fun i : ℕ => label i=m), phase (f (a+i))‖ ≤ 2*d/lam+1+2/d := by
    let F := S.filter (fun i : ℕ => label i=m)
    let near : Finset ℕ := F.filter (fun i : ℕ => g (a+i) < (m : ℝ)+d)
    let far : Finset ℕ := F.filter (fun i : ℕ => ¬g (a+i) < (m : ℝ)+d)
    have hF (i : ℕ) (hi : i ∈ F) : i ≤ N ∧
        (m : ℝ) ≤ g (a+i)+d ∧ g (a+i)+d < (m : ℝ)+1 := by
      have hmem := Finset.mem_filter.mp hi
      have hiN : i ≤ N := by have := Finset.mem_range.mp hmem.1; omega
      exact ⟨hiN, Int.floor_eq_iff.mp hmem.2⟩
    have hnear_card : (near.card : ℝ) ≤ 2*d/lam+1 := by
      have hnc := separated_slope_card_bound near (fun i : ℕ => g (a+i)) hlam
        (A := (m : ℝ)-d) (B := (m : ℝ)+d) (by
          intro i hi
          have hmem := Finset.mem_filter.mp hi
          have hfi := hF i hmem.1
          constructor <;> linarith [hmem.2]) (by
          intro i hi j hj hij
          exact sampled_derivative_separation g k a N hg hgk hk hij
            (hF j (Finset.mem_filter.mp hj).1).1)
      have he : ((m : ℝ)+d-((m : ℝ)-d))/lam+1 = 2*d/lam+1 := by ring
      rw [he, max_eq_right (by positivity : (0 : ℝ) ≤ 2*d/lam+1)] at hnc
      exact hnc
    have hnear : ‖∑ i ∈ near, phase (f (a+i))‖ ≤ 2*d/lam+1 := by
      calc
        _ ≤ ∑ i ∈ near, ‖phase (f (a+i))‖ := norm_sum_le _ _
        _ = (near.card : ℝ) := by simp only [phase_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ _ := hnear_card
    have hfar_strip (i : ℕ) (hi : i ∈ far) :
        (m : ℝ)+d ≤ g (a+i) ∧ g (a+i) ≤ (m : ℝ)+1-d := by
      have hmem := Finset.mem_filter.mp hi
      have hfi := hF i hmem.1
      constructor <;> linarith [hmem.2]
    have hfar_sub : far ⊆ Finset.range (N+1) := by
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hfar_conv : ∀ i ∈ far, ∀ j ∈ far, ∀ l, i ≤ l → l ≤ j → l ∈ far := by
      intro i hi j hj l hil hlj
      have hiF := hF i (Finset.mem_filter.mp hi).1
      have hjF := hF j (Finset.mem_filter.mp hj).1
      have hlN := hlj.trans hjF.1
      have hgli := hmono (natural_sample_mem hiF.1) (natural_sample_mem hlN) (by gcongr)
      have hgjl := hmono (natural_sample_mem hlN) (natural_sample_mem hjF.1) (by gcongr)
      have hgl : (m : ℝ)+d ≤ g (a+l) := (hfar_strip i hi).1.trans hgli
      have hlab : label l=m := Int.floor_eq_iff.mpr ⟨by linarith, by linarith [hjF.2.2]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hlab⟩, by linarith⟩
    have hfar : ‖∑ i ∈ far, phase (f (a+i))‖ ≤ 2/d :=
      first_derivative_on_indices f g a N far m d hd hdh hfar_sub hfar_conv hf hfg hmono hfar_strip
    have he : (∑ i ∈ F, phase (f (a+i))) =
        (∑ i ∈ near, phase (f (a+i))) + ∑ i ∈ far, phase (f (a+i)) := by
      exact (Finset.sum_filter_add_sum_filter_not F (fun i : ℕ => g (a+i) < (m : ℝ)+d)
        (fun i : ℕ => phase (f (a+i)))).symm
    change ‖∑ i ∈ F, phase (f (a+i))‖ ≤ _
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hnear hfar)
  have hsplit : (∑ i ∈ S, phase (f (a+i))) =
      ∑ m ∈ T, ∑ i ∈ S.filter (fun i : ℕ => label i=m), phase (f (a+i)) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem label hi)
      (fun i : ℕ => phase (f (a+i)))).symm
  rw [show (Finset.range (N+1)) = S from rfl, hsplit]
  calc
    _ ≤ ∑ m ∈ T, ‖∑ i ∈ S.filter (fun i : ℕ => label i=m), phase (f (a+i))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ T, (2*d/lam+1+2/d) := Finset.sum_le_sum (fun m _ => hfiber m)
    _ = (T.card : ℝ)*(2*d/lam+1+2/d) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hcost

end NField.Alignment.CommonResetDerivativePartition
