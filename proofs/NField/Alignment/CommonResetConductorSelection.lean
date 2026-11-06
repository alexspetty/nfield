/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetRetainedBands

/-! # Consecutive conductor selections with every literal cutoff retained -/

noncomputable section

namespace NField.Alignment.CommonResetConductorSelection

open scoped BigOperators
open Set CommonResetRetainedBands CommonResetBandWeighted CommonResetBandGeometry
open CommonResetBandParameters

def quarterCutoff (p : ℕ) : ℕ := Nat.floor ((p : ℝ)^(3/4 : ℝ))

/-- Title: `The published three-quarter conductor cutoff is above the square-root threshold`. -/
theorem sqrt_le_quarterCutoff {p : ℕ} (hp : 1 ≤ p) : Nat.sqrt p ≤ quarterCutoff p := by
  unfold quarterCutoff
  apply Nat.le_floor
  calc
    _ ≤ Real.sqrt (p : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ ≤ (p : ℝ)^(3/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) (by norm_num)

def conductorSelection (p m u v j K : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p-1)).filter (fun t => K<t ∧ (p-1)/t=m ∧ 2*u<t ∧ 2*v<t ∧ 2*j<t ∧ t∈S)

theorem conductorSelection_consecutive {p m u v j K : ℕ} (S : Finset ℕ)
    (hS : ∀ i ∈ S, ∀ k ∈ S, ∀ t, i≤t → t≤k → t∈S) :
    ∀ i ∈ conductorSelection p m u v j K S, ∀ k ∈ conductorSelection p m u v j K S,
      ∀ t, i≤t → t≤k → t ∈ conductorSelection p m u v j K S := by
  intro i hi k hk t hit htk
  have hiD := Finset.mem_filter.mp hi
  have hkD := Finset.mem_filter.mp hk
  have hiI := Finset.mem_Icc.mp hiD.1
  have hkI := Finset.mem_Icc.mp hkD.1
  have hlo : (p-1)/k ≤ (p-1)/t := Nat.div_le_div_left htk (by omega)
  have hhi : (p-1)/t ≤ (p-1)/i := Nat.div_le_div_left hit (by omega)
  have he : (p-1)/t=m := by rw [hiD.2.2.1] at hhi; rw [hkD.2.2.1] at hlo; omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    ⟨by omega, he, by omega, by omega, by omega,
      hS i hiD.2.2.2.2.2.2 k hkD.2.2.2.2.2.2 t hit htk⟩⟩

theorem conductorSelection_properties {p m u v j K : ℕ} (hm : 1 ≤ m) (S : Finset ℕ)
    (t : ℕ) (ht : t ∈ conductorSelection p m u v j K S) :
    (t : ℝ) ∈ Icc (bandLeft p m) (bandRight p m) ∧ 2*u<t ∧ 2*v<t ∧ 2*j<t := by
  have htD := Finset.mem_filter.mp ht
  exact ⟨quotient_band_membership (by have := (Finset.mem_Icc.mp htD.1).1; omega) hm htD.2.2.1,
    htD.2.2.2.1, htD.2.2.2.2.1, htD.2.2.2.2.2.1⟩

/-- Title: `The band bound applies to the published conductor cutoff and every additional interval restriction`. -/
theorem selected_band_bound {p m u v j : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (S : Finset ℕ) (hS : ∀ i ∈ S, ∀ k ∈ S, ∀ t, i≤t → t≤k → t∈S) :
    |∑ t ∈ conductorSelection p m u v j (quarterCutoff p) S, originalFrequency p t u v j| ≤
      291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j := by
  by_cases he : (conductorSelection p m u v j (quarterCutoff p) S).Nonempty
  · obtain ⟨t, ht⟩ := he
    have htD := Finset.mem_filter.mp ht
    have hlarge : Nat.sqrt p < t := (sqrt_le_quarterCutoff hp.one_le).trans_lt htD.2.1
    have hm2 : m^2 ≤ p := by
      have hh := large_conductor_quotient_square hlarge
      rwa [htD.2.2.1] at hh
    exact retained_band_bound hp hm hm2 hu hup hv hj _ (conductorSelection_consecutive S hS)
      (conductorSelection_properties hm S)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (bandSummandScale_nonneg p m u v j hu)

theorem selected_band_bound_all_u {p m u v j : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hu : 0 < u) (hv : 0 < v) (hj : 0 < j)
    (S : Finset ℕ) (hS : ∀ i ∈ S, ∀ k ∈ S, ∀ t, i≤t → t≤k → t∈S) :
    |∑ t ∈ conductorSelection p m u v j (quarterCutoff p) S, originalFrequency p t u v j| ≤
      291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j := by
  by_cases hup : 2*u < p
  · exact selected_band_bound hp hm hu hup hv hj S hS
  · have he : conductorSelection p m u v j (quarterCutoff p) S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htD := Finset.mem_filter.mp ht
      have htP := (Finset.mem_Icc.mp htD.1).2
      have hut := htD.2.2.2.1
      omega
    rw [he, Finset.sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (bandSummandScale_nonneg p m u v j hu)

end NField.Alignment.CommonResetConductorSelection
