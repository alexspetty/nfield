/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedSources

/-! # Weighted midpoint sampling on every positive grid -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedSampling

open scoped BigOperators
open MeasureTheory CommonResetGram CommonResetWeightedSources CommonResetGeneralReciprocity
open CommonResetBernoulliLifts CommonResetGrid CollisionRampEnergy
open DedekindReciprocity RademacherThreeTerm

def weightedSample (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  (1/(q : ℝ))*∑ a ∈ Finset.range q, weightedProfile N c ((a : ℝ)/q)^2

def weightedDefect (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, weightedProfile N c x^2) - weightedSample N q c

def slopeMoment (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.Icc 1 N, (j : ℝ)*c j

def curvatureMoment (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j*(j.gcd q : ℝ)^2/j

theorem weightedSample_coefficient_sum {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    weightedSample N q c = (4/(q : ℝ))*∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*(arithmeticCoefficientDedekindTerm j k q : ℝ) := by
  unfold weightedSample
  simp only [weightedProfile_square]
  rw [← Finset.mul_sum]
  rw [show (1/(q : ℝ))*(4*∑ a ∈ Finset.range q,
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c j*c k)*(midpointRow j ((a : ℝ)/q)*midpointRow k ((a : ℝ)/q))) =
      (4/(q : ℝ))*∑ a ∈ Finset.range q, ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c j*c k)*(midpointRow j ((a : ℝ)/q)*midpointRow k ((a : ℝ)/q)) by ring]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  unfold arithmeticCoefficientDedekindTerm
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [midpointRow_rational hq, midpointRow_rational hq]

theorem pair_sampling_identity {j k q : ℕ} (hj : 0 < j) (hk : 0 < k) (hq : 0 < q) :
    (j.gcd k : ℝ)^2/(3*j*k) - 4*(arithmeticCoefficientDedekindTerm j k q : ℝ)/q =
      ((j.gcd k).gcd q : ℝ)/q +
        4*((arithmeticCoefficientDedekindTerm q k j : ℝ) +
          (arithmeticCoefficientDedekindTerm q j k : ℝ))/q -
        ((j : ℝ)*(k.gcd q : ℝ)^2/k + (k : ℝ)*(j.gcd q : ℝ)^2/j)/(3*(q : ℝ)^2) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (three_modulus_reciprocity hj hk hq)
  push_cast at h
  rw [coefficient_swap k q, Nat.gcd_comm q j] at h
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hjR, hkR, hqR] at h ⊢
  nlinarith

theorem weightedInterior_symmetric (N q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*((arithmeticCoefficientDedekindTerm q k j : ℝ) +
        (arithmeticCoefficientDedekindTerm q j k : ℝ))) = weightedInterior N q c := by
  rw [weightedInterior_coefficient_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  have hs : (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*(arithmeticCoefficientDedekindTerm q j k : ℝ)) =
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j*c k*(arithmeticCoefficientDedekindTerm q k j : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  ring

theorem curvatureMoment_symmetric (N q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*((j : ℝ)*(k.gcd q : ℝ)^2/k + (k : ℝ)*(j.gcd q : ℝ)^2/j)) =
      2*slopeMoment N c*curvatureMoment N q c := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*((j : ℝ)*(k.gcd q : ℝ)^2/k)) = slopeMoment N c*curvatureMoment N q c := by
    unfold slopeMoment curvatureMoment
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsecond : (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*((k : ℝ)*(j.gcd q : ℝ)^2/j)) = slopeMoment N c*curvatureMoment N q c := by
    rw [← hfirst, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfirst, hsecond]
  ring

/-- Title: `Weighted midpoint sampling separates every reset on an arbitrary grid`. -/
theorem weighted_sampling_identity {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    weightedDefect N q c = resetMass N q c/q + 4*weightedInterior N q c/q -
      2*slopeMoment N c*curvatureMoment N q c/(3*(q : ℝ)^2) := by
  calc
    _ = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j*c k*((j.gcd k : ℝ)^2/(3*j*k) -
          4*(arithmeticCoefficientDedekindTerm j k q : ℝ)/q) := by
      rw [weightedDefect, weighted_gram, weightedSample_coefficient_sum hq]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
        apply Finset.sum_congr rfl <;> intro k _ <;> ring
    _ = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c j*c k*((j.gcd k).gcd q : ℝ)/q +
          4*(c j*c k*((arithmeticCoefficientDedekindTerm q k j : ℝ) +
            (arithmeticCoefficientDedekindTerm q j k : ℝ)))/q -
          c j*c k*((j : ℝ)*(k.gcd q : ℝ)^2/k +
            (k : ℝ)*(j.gcd q : ℝ)^2/j)/(3*(q : ℝ)^2)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [pair_sampling_identity (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1 hq]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.mul_sum]
      rw [← resetMass_gcd_sum hq, weightedInterior_symmetric, curvatureMoment_symmetric]

end NField.Alignment.CommonResetWeightedSampling
