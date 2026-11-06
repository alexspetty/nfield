/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetNaturalTails
import NField.Alignment.CommonResetFrequencyPartition

/-! # Exact source correspondence for both complete frequency tails -/

noncomputable section

namespace NField.Alignment.CommonResetTailSource

open scoped BigOperators
open CommonResetNaturalTails CommonResetNaturalFrequencies CommonResetFrequencyPartition
open CommonResetLinearTailAssembly CommonResetEndpointTailAssembly CommonResetTailGrowth

theorem sum_three_rotate {R : Type*} [AddCommMonoid R] (A B C : Finset ℕ) (f : ℕ → ℕ → ℕ → R) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c) = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c := Finset.sum_congr rfl (fun a ha => Finset.sum_comm)
    _ = _ := Finset.sum_comm

def tailSelection (p K u a : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p-1)).filter (fun t => K<t ∧ 2*u<t ∧ 2*a<t ∧ u.Coprime t)

theorem tailSelection_properties (p K u a t : ℕ) (ht : t ∈ tailSelection p K u a) :
    2 ≤ t ∧ t < p ∧ 2*u<t ∧ 2*a<t ∧ u.Coprime t := by
  have htD := Finset.mem_filter.mp ht
  have htI := Finset.mem_Icc.mp htD.1
  exact ⟨htI.1, by omega, htD.2.2.1, htD.2.2.2.1, htD.2.2.2.2⟩

theorem linear_slice_gate {p t u j : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (hj : 0 < j)
    (start length : ℕ) (hs : 0 < start) :
    (∑ a ∈ Finset.range length, naturalFrequency p t u (start+a) j) =
      if 2*u<t ∧ 2*j<t ∧ u.Coprime t then naturalLinearTail (p-1) (p^2) t u j start length else 0 := by
  by_cases hc : u.Coprime t
  · by_cases huT : 2*u<t
    · by_cases hjT : 2*j<t
      · rw [if_pos ⟨huT, hjT, hc⟩]
        exact natural_linear_slice hp ht huT hj hjT start length hs
      · simp only [hjT, and_false, false_and, if_false, naturalFrequency, Finset.sum_const_zero]
    · simp only [huT, false_and, if_false, naturalFrequency, Finset.sum_const_zero]
  · simp only [hc, and_false, if_false, naturalFrequency_nonunit p t u _ j hc, Finset.sum_const_zero]

theorem endpoint_slice_gate {p t u v : ℕ} (hp : 2 ≤ p) (ht : 0 < t)
    (start length : ℕ) (hs : 0 < start) :
    (∑ a ∈ Finset.range length, naturalFrequency p t u v (start+a)) =
      if 2*u<t ∧ 2*v<t ∧ u.Coprime t then naturalEndpointTail p t u v start length else 0 := by
  by_cases hc : u.Coprime t
  · by_cases huT : 2*u<t
    · by_cases hvT : 2*v<t
      · rw [if_pos ⟨huT, hvT, hc⟩]
        exact natural_endpoint_slice hp ht huT hvT start length hs
      · simp only [hvT, and_false, false_and, if_false, naturalFrequency, Finset.sum_const_zero]
    · simp only [huT, false_and, if_false, naturalFrequency, Finset.sum_const_zero]
  · simp only [hc, and_false, if_false, naturalFrequency_nonunit p t u v _ hc, Finset.sum_const_zero]

/-- Title: `The original complete linear-frequency source tail equals its selected-tail representation`. -/
theorem largeLinearSource_eq_tail {p : ℕ} (hp : 2 ≤ p) (K V : ℕ) :
    largeLinearSource p K V = selectedLinearTail p (halfPrime p) (halfPrime p) (V+1)
      (tailSelection p K) (fun _ _ _ => halfPrime p-V) := by
  unfold largeLinearSource linearSlice selectedLinearTail
  simp_rw [tailSelection, Finset.sum_filter]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro t ht
  have ht0 : 0 < t := by have := (Finset.mem_Icc.mp ht).1; omega
  by_cases hKt : K<t
  · rw [if_pos hKt]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum]
    rw [linear_slice_gate hp ht0 (Finset.mem_Icc.mp hj).1 (V+1) (halfPrime p-V) (by omega)]
    by_cases hc : 2*u<t ∧ 2*j<t ∧ u.Coprime t <;>
      simp only [hKt, hc, true_and, if_false, mul_zero, mul_ite]
  · simp only [hKt, false_and, if_false, Finset.sum_const_zero]

/-- Title: `The original complete endpoint-frequency source tail equals its selected-tail representation`. -/
theorem largeEndpointSource_eq_tail {p : ℕ} (hp : 2 ≤ p) (K V J : ℕ) :
    largeEndpointSource p K V J = selectedEndpointTail p (halfPrime p) V (J+1)
      (tailSelection p K) (fun _ _ _ => halfPrime p-J) := by
  unfold largeEndpointSource endpointSlice selectedEndpointTail
  simp_rw [tailSelection, Finset.sum_filter]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro t ht
  have ht0 : 0 < t := by have := (Finset.mem_Icc.mp ht).1; omega
  by_cases hKt : K<t
  · rw [if_pos hKt]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.mul_sum]
    rw [endpoint_slice_gate hp ht0 (J+1) (halfPrime p-J) (by omega)]
    by_cases hc : 2*u<t ∧ 2*v<t ∧ u.Coprime t <;>
      simp only [hKt, hc, true_and, if_false, mul_zero, mul_ite]
  · simp only [hKt, false_and, if_false, Finset.sum_const_zero]

/-- Title: `The entire linear tail of the original source has its published cutoff bound`. -/
theorem large_linear_source_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p K V : ℕ, p.Prime → 0 < V →
      |largeLinearSource p K V| ≤ C*(p : ℝ)^(2+ε)/(V : ℝ) := by
  obtain ⟨C, hC, hc⟩ := linear_frequency_tail ε hε
  refine ⟨C, hC, ?_⟩
  intro p K V hp hV
  rw [largeLinearSource_eq_tail hp.two_le]
  have hP : halfPrime p < p := by have := halfPrime_lt hp.one_le; omega
  exact hc p hp (halfPrime p) (halfPrime p) V hP hP hV _ _
    (fun u hu j hj t ht => tailSelection_properties p K u j t ht)

/-- Title: `The entire linked endpoint tail of the original source has its published cutoff bound`. -/
theorem large_endpoint_source_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p K V J : ℕ, p.Prime → V ≤ halfPrime p → 0 < J →
      |largeEndpointSource p K V J| ≤ C*(p : ℝ)^(2+ε)/(J : ℝ) := by
  obtain ⟨C, hC, hc⟩ := endpoint_frequency_tail ε hε
  refine ⟨C, hC, ?_⟩
  intro p K V J hp hV hJ
  rw [largeEndpointSource_eq_tail hp.two_le]
  have hV' : 2*V < p := (Nat.mul_le_mul_left 2 hV).trans_lt (halfPrime_lt hp.one_le)
  exact hc p hp (halfPrime p) V J (halfPrime_lt hp.one_le) hV' hJ _ _
    (fun u hu v hv t ht => tailSelection_properties p K u v t ht)

end NField.Alignment.CommonResetTailSource
