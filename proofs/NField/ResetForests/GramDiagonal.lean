/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Dilation
/-! # The full sampled source Gram and its exact harmonic trace -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.GramDecomposition

open scoped BigOperators Matrix
open NField.Alignment CommonResetGram CollisionRampEnergy CollisionRemainderCovariance
open SourceMetrics FibreReconstruction

theorem midpoint_one_grid_square {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑ a ∈ Finset.range Q, (2*midpointRow 1 ((a : ℝ)/(Q : ℝ)))^2)=
      ((Q : ℝ)-1)*((Q : ℝ)-2)/(3*(Q : ℝ)) := by
  have hQpos : 0 < Q := by omega
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hpoint (a : ℕ) (ha : a ∈ Finset.range Q) :
      (2*midpointRow 1 ((a : ℝ)/(Q : ℝ)))^2=
        (2*(a : ℝ)/(Q : ℝ)-1)^2-(if a=0 then 1 else 0) := by
    by_cases ha0 : a=0
    · subst a
      simp [midpointRow]
    · have hrow := midpoint_row_grid_quotient hQpos (Nat.coprime_one_left Q)
        (Nat.pos_of_ne_zero ha0) (Finset.mem_range.mp ha)
      simp only [one_mul, Nat.div_eq_of_lt (Finset.mem_range.mp ha), Nat.cast_zero,
        sub_zero] at hrow
      rw [hrow, if_neg ha0]
      ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hzero : (∑ a ∈ Finset.range Q, if a=0 then (1 : ℝ) else 0)=1 := by simp [hQpos]
  rw [hzero]
  have hexpand : (∑ a ∈ Finset.range Q, (2*(a : ℝ)/(Q : ℝ)-1)^2)=
      (4/(Q : ℝ)^2)*(∑ a ∈ Finset.range Q, (a : ℝ)^2)-
        (4/(Q : ℝ))*(∑ a ∈ Finset.range Q, (a : ℝ))+(Q : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hc : (Q : ℝ)=∑ a ∈ Finset.range Q, (1 : ℝ) := by simp
    rw [hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hexpand, sum_range_real_id, sum_range_real_sq]
  field_simp
  ring

theorem midpoint_harmonic_grid_square {Q j : ℕ} (hQ : 2 ≤ Q) (hj : j.Coprime Q) :
    (∑ a ∈ Finset.range Q, (2*midpointRow j ((a : ℝ)/(Q : ℝ)))^2)=
      ((Q : ℝ)-1)*((Q : ℝ)-2)/(3*(Q : ℝ)) := by
  have hf : Function.Periodic (fun x => (2*midpointRow 1 x)^2) 1 := by
    intro x
    change (2*midpointRow 1 (x+1))^2=(2*midpointRow 1 x)^2
    rw [midpointRow_periodic]
  have hpoint (a : ℕ) : midpointRow j ((a : ℝ)/(Q : ℝ))=
      midpointRow 1 ((j : ℝ)*((a : ℝ)/(Q : ℝ))) := by
    simp only [midpointRow, affineRow, Nat.cast_one, one_mul]
  simp_rw [hpoint]
  rw [periodic_complete_grid_dilation (by omega : 0 < Q) hj hf]
  exact midpoint_one_grid_square hQ

theorem sampled_gram_diagonal {N Q : ℕ} (hQ : 2 ≤ Q) (i : Fin N)
    (hi : (i.val+1).Coprime Q) :
    sampledGram N Q i i=((Q : ℝ)-1)*((Q : ℝ)-2)/(3*(Q : ℝ)) := by
  rw [sampled_gram_entry]
  simp only [weighted_profile_basis, ← pow_two]
  rw [Fin.sum_univ_eq_sum_range
    (fun a : ℕ => (2*midpointRow (i.val+1) ((a : ℝ)/(Q : ℝ)))^2) Q]
  exact midpoint_harmonic_grid_square hQ hi

theorem sampled_gram_trace {N Q : ℕ} (hQ : 2 ≤ Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) :
    Matrix.trace (sampledGram N Q)=
      (N : ℝ)*((Q : ℝ)-1)*((Q : ℝ)-2)/(3*(Q : ℝ)) := by
  have hdiag (i : Fin N) : sampledGram N Q i i=
      ((Q : ℝ)-1)*((Q : ℝ)-2)/(3*(Q : ℝ)) :=
    sampled_gram_diagonal hQ i (hunit (i.val+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  simp only [Matrix.trace, Matrix.diag_apply]
  simp_rw [hdiag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem prime_square_gram_trace {p : ℕ} (hp : p.Prime) :
    Matrix.trace (sampledGram (p-1) (p^2))=
      ((p-1 : ℕ) : ℝ)*((p : ℝ)^2-1)*((p : ℝ)^2-2)/(3*(p : ℝ)^2) := by
  simpa only [Nat.cast_pow] using sampled_gram_trace
    (by nlinarith [hp.two_le] : 2 ≤ p^2) (fun j hj => prime_square_source_units hp hj)

theorem sampled_gram_mixed (N Q : ℕ) (c e : Fin N → ℝ) :
    c ⬝ᵥ (sampledGram N Q *ᵥ e)=
      ∑ a : Fin Q,
        weightedProfile N (cutoffCoefficients N c) ((a.val : ℝ)/(Q : ℝ))*
          weightedProfile N (cutoffCoefficients N e) ((a.val : ℝ)/(Q : ℝ)) := by
  have htranspose : (samplingMatrix N Q)ᴴ=(samplingMatrix N Q)ᵀ := by
    ext a i
    simp
  rw [sampledGram, htranspose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]
  simp only [dotProduct, sampling_matrix_reading]

theorem sampled_gram_mixed_normalized (N : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (c e : Fin N → ℝ) :
    c ⬝ᵥ (sampledGram N Q *ᵥ e)=
      (Q : ℝ)*sampledWork N Q (cutoffCoefficients N c) (cutoffCoefficients N e) := by
  rw [sampled_gram_mixed, sampledWork]
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [Fin.sum_univ_eq_sum_range
    (fun a : ℕ => weightedProfile N (cutoffCoefficients N c) ((a : ℝ)/(Q : ℝ))*
      weightedProfile N (cutoffCoefficients N e) ((a : ℝ)/(Q : ℝ))) Q]
  field_simp

theorem cutoff_complete_profile (N : ℕ) (x : ℝ) :
    weightedProfile N (cutoffCoefficients N (fun _ => 1)) x=
      weightedProfile N (fun _ => 1) x := by
  unfold weightedProfile
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [cutoffCoefficients, dif_pos hj]

end NField.ResetForests.GramDecomposition
