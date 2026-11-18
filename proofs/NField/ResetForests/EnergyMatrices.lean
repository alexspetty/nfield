/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ContinuousPositive
/-! # The actual positive definite cutoff energy matrices

Source coordinates are indexed by Fin N and correspond exactly to
harmonics1 throughN. The sampled matrix includes allQ rows.
-/

noncomputable section

namespace NField.ResetForests.SourceMetrics

open scoped BigOperators Matrix
open NField.Alignment CommonResetGram CollisionRampEnergy

def cutoffCoefficients (N : ℕ) (c : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j ∈ Finset.Icc 1 N then c ⟨j-1, by have := Finset.mem_Icc.mp hj; omega⟩ else 0

theorem cutoff_coefficients_succ (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    cutoffCoefficients N c (i.val+1)=c i := by
  simp only [cutoffCoefficients, Finset.mem_Icc, Nat.add_sub_cancel]
  rw [dif_pos (by omega)]

theorem sum_source_indices (N : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 N, f j)=∑ i : Fin N, f (i.val+1) := by
  refine Finset.sum_bij (fun j hj => (⟨j-1, by have := Finset.mem_Icc.mp hj; omega⟩ : Fin N))
    (fun j hj => Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb he
    have hv := congrArg Fin.val he
    have := Finset.mem_Icc.mp ha
    have := Finset.mem_Icc.mp hb
    dsimp at hv
    omega
  · intro i _
    refine ⟨i.val+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp
  · intro j hj
    congr 1
    have := (Finset.mem_Icc.mp hj).1
    dsimp
    omega

theorem weighted_profile_fin (N : ℕ) (c : Fin N → ℝ) (x : ℝ) :
    weightedProfile N (cutoffCoefficients N c) x=
      2*∑ i : Fin N, c i*midpointRow (i.val+1) x := by
  rw [weightedProfile, sum_source_indices]
  simp only [cutoff_coefficients_succ]

theorem weighted_profile_basis (N : ℕ) (i : Fin N) (x : ℝ) :
    weightedProfile N (cutoffCoefficients N (Pi.single i 1)) x=2*midpointRow (i.val+1) x := by
  rw [weighted_profile_fin]
  simp [Pi.single_apply]

def continuousGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Nat.gcd (i.val+1) (j.val+1) : ℝ)^2/
    (3*((i.val+1 : ℕ) : ℝ)*((j.val+1 : ℕ) : ℝ))

def samplingMatrix (N Q : ℕ) : Matrix (Fin Q) (Fin N) ℝ :=
  fun a i => 2*midpointRow (i.val+1) ((a.val : ℝ)/(Q : ℝ))

def sampledGram (N Q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (samplingMatrix N Q)ᴴ*samplingMatrix N Q

theorem continuous_gram_entry (N : ℕ) (i j : Fin N) :
    continuousGram N i j = ∫ x in (0 : ℝ)..1,
      weightedProfile N (cutoffCoefficients N (Pi.single i 1)) x*
        weightedProfile N (cutoffCoefficients N (Pi.single j 1)) x := by
  simp_rw [weighted_profile_basis,
    show ∀ a b : ℝ, (2*a)*(2*b)=4*(a*b) from by intros; ring]
  rw [intervalIntegral.integral_const_mul,
    midpoint_ramp_gram (by omega : 0 < i.val+1) (by omega : 0 < j.val+1)]
  unfold continuousGram
  field_simp
  norm_num

theorem sampled_gram_entry (N Q : ℕ) (i j : Fin N) :
    sampledGram N Q i j = ∑ a : Fin Q,
      weightedProfile N (cutoffCoefficients N (Pi.single i 1)) ((a.val : ℝ)/(Q : ℝ))*
        weightedProfile N (cutoffCoefficients N (Pi.single j 1)) ((a.val : ℝ)/(Q : ℝ)) := by
  simp only [sampledGram, Matrix.mul_apply, Matrix.conjTranspose_apply, samplingMatrix,
    star_trivial, weighted_profile_basis]

theorem sampling_matrix_reading (N Q : ℕ) (c : Fin N → ℝ) (a : Fin Q) :
    (samplingMatrix N Q *ᵥ c) a =
      weightedProfile N (cutoffCoefficients N c) ((a.val : ℝ)/(Q : ℝ)) := by
  simp only [samplingMatrix, Matrix.mulVec, dotProduct, weighted_profile_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem continuous_gram_quadratic (N : ℕ) (c : Fin N → ℝ) :
    star c ⬝ᵥ (continuousGram N *ᵥ c)=
      ∫ x in (0 : ℝ)..1, weightedProfile N (cutoffCoefficients N c) x^2 := by
  rw [weighted_gram]
  simp_rw [sum_source_indices, cutoff_coefficients_succ]
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, continuousGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi : (0 : ℝ) < ((i.val+1 : ℕ) : ℝ) := by positivity
  have hj : (0 : ℝ) < ((j.val+1 : ℕ) : ℝ) := by positivity
  field_simp

theorem continuous_gram_hermitian (N : ℕ) : (continuousGram N).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, continuousGram, star_trivial, Nat.gcd_comm]
  ring

theorem sampling_matrix_injective {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) :
    Function.Injective (samplingMatrix N Q).mulVec := by
  intro c d he
  have hzero : samplingMatrix N Q *ᵥ (c-d)=0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have hs : ∀ a ∈ Finset.range Q,
      weightedProfile N (cutoffCoefficients N (c-d)) ((a : ℝ)/(Q : ℝ))=0 := by
    intro a ha
    have hz := congrFun hzero ⟨a, Finset.mem_range.mp ha⟩
    simpa only [sampling_matrix_reading, Pi.zero_apply] using hz
  have hc := sampled_field_injective hN hQ _ hunit hs
  funext i
  have hi := hc (i.val+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [cutoff_coefficients_succ, Pi.sub_apply] at hi
  exact sub_eq_zero.mp hi

theorem cutoff_continuous_gram_posDef {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) : (continuousGram N).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (continuous_gram_hermitian N)
  intro c hc
  rw [continuous_gram_quadratic]
  apply continuous_work_positive hN hQ _ hunit
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  refine ⟨i.val+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  simpa only [cutoff_coefficients_succ, Pi.zero_apply] using hi

theorem cutoff_sampled_gram_posDef {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) : (sampledGram N Q).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (sampling_matrix_injective hN hQ hunit)

theorem both_prime_square_grams_posDef {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (continuousGram (p-1)).PosDef ∧ (sampledGram (p-1) (p^2)).PosDef := by
  have hN : 2 ≤ p-1 := by have := hp.two_le; omega
  have hQ : (p-1)^2 < p^2 := by nlinarith [Nat.sub_add_cancel hp.one_le]
  exact ⟨cutoff_continuous_gram_posDef hN hQ (fun j hj => prime_square_source_units hp hj),
    cutoff_sampled_gram_posDef hN hQ (fun j hj => prime_square_source_units hp hj)⟩

end NField.ResetForests.SourceMetrics
