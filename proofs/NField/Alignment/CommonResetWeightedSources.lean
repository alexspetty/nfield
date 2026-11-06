/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetGeneralReciprocity

/-! # Exact weighted reset mass and interior source -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedSources

open scoped BigOperators
open CommonResetGram CommonResetDedekind CommonResetGrid CollisionRampEnergy
open EndpointReciprocityBridge DedekindReciprocity RademacherThreeTerm

def resetWeight (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, if d ∣ j then c j else 0

def resetMass (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ q.divisors.filter (fun d => d ≤ N), (d.totient : ℝ)*resetWeight N c d^2

def weightedInterior (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, resetWeight N c d *
    ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      weightedProfile N c ((a : ℝ)/d)*midpointRow q ((a : ℝ)/d)

theorem weighted_divisor_columns (N : ℕ) (c f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, c k * ∑ d ∈ k.divisors, f d) =
      ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*f d := by
  classical
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        (if d ∣ k then c k else 0)*f d := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkd := Finset.mem_Icc.mp hk
      have hset : k.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ k) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro h
          exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hkd.1,
            (Nat.le_of_dvd hkd.1 h.1).trans hkd.2⟩, h.1⟩
        · intro h
          exact ⟨h.2, by omega⟩
      rw [hset, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (if d ∣ k then c k else 0)*f d := Finset.sum_comm
    _ = _ := by simp only [resetWeight, Finset.sum_mul]

theorem weighted_coefficient_columns (N q j : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, c k*(arithmeticCoefficientDedekindTerm q j k : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*(primitiveCoefficientCorrelation q j d : ℝ) := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, c k*∑ d ∈ k.divisors,
        (primitiveCoefficientCorrelation q j d : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [arithmeticCoefficientDedekindTerm_eq_primitiveDivisorSum (Finset.mem_Icc.mp hk).1]
      push_cast
      rfl
    _ = _ := weighted_divisor_columns N c _

theorem weighted_source_row {d : ℕ} (hd : 2 ≤ d) (N q : ℕ) (c : ℕ → ℝ) :
    (∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      weightedProfile N c ((a : ℝ)/d)*midpointRow q ((a : ℝ)/d)) =
      2 * ∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j d : ℝ) := by
  unfold weightedProfile
  simp only [Finset.mul_sum, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← BernoulliCurvature.reducedResidues_eq_Ico hd]
  unfold primitiveCoefficientCorrelation
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [midpointRow_rational (by omega : 0 < d), midpointRow_rational (by omega : 0 < d)]
  ring

/-- Title: `Weighted interior readings equal the entire coefficient double sum`. -/
theorem weightedInterior_coefficient_sum (N q : ℕ) (c : ℕ → ℝ) :
    weightedInterior N q c = 2*∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      c k*c j*(arithmeticCoefficientDedekindTerm q j k : ℝ) := by
  have hzero : resetWeight N c 1 *
      (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j 1 : ℝ)) = 0 := by
    simp only [primitiveCorrelation_one, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
  calc
    _ = ∑ d ∈ Finset.Icc 2 N, resetWeight N c d *
        (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j d : ℝ)) := by
      unfold weightedInterior
      apply Finset.sum_congr rfl
      intro d hd
      rw [weighted_source_row (Finset.mem_Icc.mp hd).1]
    _ = ∑ d ∈ Finset.Icc 1 N, resetWeight N c d *
        (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j d : ℝ)) :=
      sum_Icc_remove_one N _ hzero
    _ = 2*∑ j ∈ Finset.Icc 1 N, c j *
        ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*(primitiveCoefficientCorrelation q j d : ℝ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = 2*∑ j ∈ Finset.Icc 1 N, c j *
        ∑ k ∈ Finset.Icc 1 N, c k*(arithmeticCoefficientDedekindTerm q j k : ℝ) := by
      simp only [weighted_coefficient_columns]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem resetWeight_square (N d : ℕ) (c : ℕ → ℝ) :
    resetWeight N c d^2 = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      if d ∣ j ∧ d ∣ k then c j*c k else 0 := by
  rw [resetWeight, pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

theorem common_reset_totient_sum {N q j k : ℕ} (hq : 0 < q)
    (hj : j ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
    (∑ d ∈ q.divisors.filter (fun d => d ≤ N),
      if d ∣ j ∧ d ∣ k then (d.totient : ℝ) else 0) = ((j.gcd k).gcd q : ℝ) := by
  have hset : (q.divisors.filter (fun d => d ≤ N)).filter (fun d => d ∣ j ∧ d ∣ k) =
      ((j.gcd k).gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨⟨hdq, _⟩, _⟩, hdj, hdk⟩
      exact ⟨⟨⟨hdj, hdk⟩, hdq⟩, (Nat.gcd_pos_of_pos_right _ hq).ne'⟩
    · rintro ⟨⟨⟨hdj, hdk⟩, hdq⟩, _⟩
      exact ⟨⟨⟨hdq, hq.ne'⟩,
        (Nat.le_of_dvd (Finset.mem_Icc.mp hj).1 hdj).trans (Finset.mem_Icc.mp hj).2⟩, hdj, hdk⟩
  rw [← Finset.sum_filter, hset]
  exact_mod_cast Nat.sum_totient ((j.gcd k).gcd q)

/-- Title: `The sampled reset mass is the full common-divisor quadratic form`. -/
theorem resetMass_gcd_sum {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    resetMass N q c = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*((j.gcd k).gcd q : ℝ) := by
  unfold resetMass
  simp only [resetWeight_square, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← common_reset_totient_sum hq hj hk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> ring

end NField.Alignment.CommonResetWeightedSources
