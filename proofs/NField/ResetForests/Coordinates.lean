/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
/-! # Reset selection in finite source coordinates

The source of a saturated reset forest is computed from the actual gcd
collapse of each source column. The reset-mask law is derived by exchanging
finite sums; no mask/source correspondence is assumed.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators

def sourceIndices (N : ℕ) : Finset ℕ := Finset.Icc 1 N

def resetMass (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ sourceIndices N, if k ∣ j then c j else 0

def collapseSource (N Ω : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ j ∈ sourceIndices N, if j.gcd Ω = d then c j else 0

theorem gcd_mem_source {N Ω j : ℕ} (hj : j ∈ sourceIndices N) :
    j.gcd Ω ∈ sourceIndices N := by
  obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp hj
  exact Finset.mem_Icc.mpr
    ⟨Nat.gcd_pos_of_pos_left Ω hpos, (Nat.gcd_le_left Ω hpos).trans hle⟩

/-- The literal gcd source sends precisely the selected reset masses. -/
theorem collapse_reset_mass (N Ω : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    resetMass N (collapseSource N Ω c) k =
      if k ∣ Ω then resetMass N c k else 0 := by
  classical
  unfold resetMass collapseSource
  have hpull (d : ℕ) :
      (if k ∣ d then (∑ j ∈ sourceIndices N,
        if j.gcd Ω = d then c j else 0) else 0) =
      ∑ j ∈ sourceIndices N,
        if k ∣ d then (if j.gcd Ω = d then c j else 0) else 0 := by
    by_cases hk : k ∣ d <;> simp [hk]
  simp_rw [hpull]
  rw [Finset.sum_comm]
  have hsingle (j : ℕ) (hj : j ∈ sourceIndices N) :
      (∑ d ∈ sourceIndices N, if k ∣ d then
        (if j.gcd Ω = d then c j else 0) else 0) =
          if k ∣ j ∧ k ∣ Ω then c j else 0 := by
    have heq (d : ℕ) :
        (if k ∣ d then (if j.gcd Ω = d then c j else 0) else 0) =
          if j.gcd Ω = d then (if k ∣ j.gcd Ω then c j else 0) else 0 := by
      by_cases h : j.gcd Ω = d <;> simp [h]
    simp_rw [heq]
    rw [Finset.sum_ite_eq]
    simp [gcd_mem_source hj, Nat.dvd_gcd_iff]
  rw [Finset.sum_congr rfl hsingle]
  by_cases hk : k ∣ Ω
  · simp [hk]
  · simp [hk]

/-- Gcd collapse conserves the complete signed source mass. -/
theorem collapse_total_mass (N Ω : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ sourceIndices N, collapseSource N Ω c d) =
      ∑ j ∈ sourceIndices N, c j := by
  classical
  unfold collapseSource
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [gcd_mem_source hj]

theorem collapse_supported (N Ω : ℕ) (c : ℕ → ℝ) {d : ℕ}
    (hd : ¬ d ∣ Ω) : collapseSource N Ω c d = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  have h : j.gcd Ω ≠ d := fun h => hd (h ▸ Nat.gcd_dvd_right j Ω)
  simp [h]

/-- Every reset-mass map is injective on its actual finite source support. -/
theorem reset_mass_injective (N : ℕ) {c e : ℕ → ℝ}
    (h : ∀ k ∈ sourceIndices N, resetMass N c k = resetMass N e k) :
    ∀ j ∈ sourceIndices N, c j = e j := by
  classical
  have hind : ∀ m : ℕ, ∀ j : ℕ, N - j = m →
      j ∈ sourceIndices N → c j = e j := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hjm hj
      have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
      have hsum :
          (∑ k ∈ sourceIndices N,
            ((if j ∣ k then c k else 0) - (if j ∣ k then e k else 0))) =
            c j - e j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro k hk hkj
          by_cases hdiv : j ∣ k
          · have hjk : j < k := lt_of_le_of_ne
              (Nat.le_of_dvd (Finset.mem_Icc.mp hk).1 hdiv) (Ne.symm hkj)
            have hkN := (Finset.mem_Icc.mp hk).2
            have heq := ih (N-k) (by omega) k rfl hk
            simp [hdiv, heq]
          · simp [hdiv]
        · exact fun hn => (hn hj).elim
      have hz := sub_eq_zero.mpr (h j hj)
      unfold resetMass at hz
      rw [← Finset.sum_sub_distrib, hsum] at hz
      exact sub_eq_zero.mp hz
  intro j hj
  exact hind (N-j) j rfl hj

/-- A reset mask determines its finite source uniquely. -/
theorem collapse_source_unique (N Ω : ℕ) (c e : ℕ → ℝ)
    (he : ∀ k ∈ sourceIndices N, resetMass N e k =
      if k ∣ Ω then resetMass N c k else 0) :
    ∀ j ∈ sourceIndices N, e j = collapseSource N Ω c j := by
  apply reset_mass_injective N
  intro k hk
  rw [he k hk, collapse_reset_mass]

/-- Repeating the same reset selection leaves the source unchanged. -/
theorem collapse_idempotent (N Ω : ℕ) (c : ℕ → ℝ) :
    ∀ j ∈ sourceIndices N,
      collapseSource N Ω (collapseSource N Ω c) j = collapseSource N Ω c j := by
  apply reset_mass_injective N
  intro k _
  simp only [collapse_reset_mass]
  split_ifs <;> rfl

theorem collapse_nonneg (N Ω d : ℕ) (c : ℕ → ℝ)
    (hc : ∀ j ∈ sourceIndices N, 0 ≤ c j) :
    0 ≤ collapseSource N Ω c d := by
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact hc j hj
  · rfl

theorem unit_reset_mass (N d : ℕ) :
    resetMass N (fun _ => 1) d = ((N/d : ℕ) : ℝ) := by
  unfold resetMass
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have heq : (sourceIndices N).filter (fun j => d ∣ j) =
      (Finset.range (N+1)).filter (fun j => j ≠ 0 ∧ d ∣ j) := by
    ext j
    simp only [Finset.mem_filter, sourceIndices, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [heq, Nat.card_multiples']

/-- Every collapse fibre uses only actual multiples of its root. -/
theorem collapse_unit_le (N Ω d : ℕ) :
    collapseSource N Ω (fun _ => 1) d ≤ ((N/d : ℕ) : ℝ) := by
  rw [← unit_reset_mass N d]
  apply Finset.sum_le_sum
  intro j _
  by_cases hg : j.gcd Ω = d
  · have hdj : d ∣ j := hg ▸ Nat.gcd_dvd_left j Ω
    simp [hg, hdj]
  · simp only [hg, ite_false]
    split_ifs <;> norm_num

/-- A forest root itself supplies a member of its collapse fibre. -/
theorem collapse_unit_ge_one {N Ω d : ℕ}
    (hd : d ∈ sourceIndices N) (hdiv : d ∣ Ω) :
    1 ≤ collapseSource N Ω (fun _ => 1) d := by
  have hg : d.gcd Ω = d := Nat.gcd_eq_left hdiv
  have hm := Finset.single_le_sum
    (f := fun j => if j.gcd Ω = d then (1 : ℝ) else 0)
    (fun j _ => by split_ifs <;> norm_num) hd
  change 1 ≤ ∑ j ∈ sourceIndices N, if j.gcd Ω = d then (1 : ℝ) else 0
  simpa only [hg, ite_true] using hm

end NField.ResetForests.Core
