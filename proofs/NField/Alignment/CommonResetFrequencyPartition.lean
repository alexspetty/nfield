/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetNaturalFrequencies
import NField.Alignment.CommonResetConductorSelection

/-! # Exact disjoint partition of the complete signed frequency source -/

noncomputable section

namespace NField.Alignment.CommonResetFrequencyPartition

open scoped BigOperators
open CommonResetNaturalFrequencies CommonResetConductorSelection CommonResetFrequencies
open CommonResetSampling

def halfPrime (p : ℕ) : ℕ := (p-1)/2

theorem halfPrime_lt {p : ℕ} (hp : 1 ≤ p) : 2*halfPrime p < p := by unfold halfPrime; omega

theorem halfPrime_covers {p t : ℕ} (htp : t ≤ p-1) : t ≤ 2*halfPrime p+1 := by unfold halfPrime; omega

theorem sum_split_cutoff {R : Type*} [AddCommMonoid R] (f : ℕ → R) {n k : ℕ} (hkn : k ≤ n) :
    (∑ x ∈ Finset.Icc 1 n, f x) =
      (∑ x ∈ Finset.Icc 1 k, f x)+(∑ i ∈ Finset.range (n-k), f (k+1+i)) := by
  have h := Finset.sum_Ico_consecutive f (by omega : 1 ≤ k+1) (by omega : k+1 ≤ n+1)
  have hmid : (∑ x ∈ Finset.Ico (k+1) (n+1), f x) =
      ∑ i ∈ Finset.range (n-k), f (k+1+i) := by
    rw [Finset.sum_Ico_eq_sum_range, show n+1-(k+1)=n-k by omega]
  rw [hmid] at h
  simpa only [Finset.Ico_add_one_right_eq_Icc] using h.symm

def linearSlice (p t V : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (halfPrime p), ∑ j ∈ Finset.Icc 1 (halfPrime p),
    ∑ a ∈ Finset.range (halfPrime p-V), naturalFrequency p t u (V+1+a) j

def endpointSlice (p t V J : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (halfPrime p), ∑ v ∈ Finset.Icc 1 V,
    ∑ a ∈ Finset.range (halfPrime p-J), naturalFrequency p t u v (J+1+a)

def boxSlice (p t V J : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (halfPrime p), ∑ v ∈ Finset.Icc 1 V,
    ∑ j ∈ Finset.Icc 1 J, naturalFrequency p t u v j

theorem completeFrequencies_partition {p t V J : ℕ} (hp : 2 ≤ p) (ht : 2 ≤ t)
    (htp : t ≤ p-1) (hV : V ≤ halfPrime p) (hJ : J ≤ halfPrime p) :
    completeFrequencies (p-1) (p^2) t = (harmonic ((p-1)/t) : ℝ)*
      (linearSlice p t V+endpointSlice p t V J+boxSlice p t V J) := by
  rw [completeFrequencies_uniform hp ht (halfPrime_covers htp)]
  unfold linearSlice endpointSlice boxSlice
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [sum_split_cutoff (fun v => ∑ j ∈ Finset.Icc 1 (halfPrime p), naturalFrequency p t u v j) hV]
  have hsmall : (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 (halfPrime p), naturalFrequency p t u v j) =
      (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, naturalFrequency p t u v j)+
        ∑ v ∈ Finset.Icc 1 V, ∑ a ∈ Finset.range (halfPrime p-J), naturalFrequency p t u v (J+1+a) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => sum_split_cutoff (fun j => naturalFrequency p t u v j) hJ)
  rw [hsmall, Finset.sum_comm (s := Finset.range (halfPrime p-V))]
  ring

def smallSource (p K : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 (p-1), if t≤K then completeFrequencies (p-1) (p^2) t else 0

def largeLinearSource (p K V : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 (p-1), if K<t then (harmonic ((p-1)/t) : ℝ)*linearSlice p t V else 0

def largeEndpointSource (p K V J : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 (p-1), if K<t then (harmonic ((p-1)/t) : ℝ)*endpointSlice p t V J else 0

def largeBoxSource (p K V J : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 (p-1), if K<t then (harmonic ((p-1)/t) : ℝ)*boxSlice p t V J else 0

theorem prime_square_coprime_below {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    (p^2).Coprime k := by
  have hc : p.Coprime k := hp.coprime_iff_not_dvd.mpr (fun hd =>
    (not_le_of_gt hkp) (Nat.le_of_dvd hk hd))
  exact hc.pow_left 2

/-- Title: `The complete signed source splits into four disjoint parts with no frequency omitted`. -/
theorem full_source_partition {p V J : ℕ} (hp : p.Prime) (K : ℕ)
    (hV : V ≤ halfPrime p) (hJ : J ≤ halfPrime p) :
    interiorSource (p-1) (p^2) = smallSource p K+largeLinearSource p K V+
      largeEndpointSource p K V J+largeBoxSource p K V J := by
  have hp1 := hp.one_le
  rw [complete_frequency_source (p-1) (p^2) (fun k hk => prime_square_coprime_below hp
    (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega))]
  unfold smallSource largeLinearSource largeEndpointSource largeBoxSource
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htK : t≤K
  · simp only [htK, not_lt_of_ge htK, if_true, if_false, add_zero]
  · have htK' : K<t := by omega
    simp only [if_neg htK, if_pos htK', zero_add]
    rw [completeFrequencies_partition hp.two_le (Finset.mem_Icc.mp ht).1
      (Finset.mem_Icc.mp ht).2 hV hJ]
    ring

end NField.Alignment.CommonResetFrequencyPartition
