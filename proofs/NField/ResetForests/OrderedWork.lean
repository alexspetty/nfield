/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.Alignment.CommonResetWeightedSampling
import Mathlib
/-! # Ordered work with the complete source retained

The reset-selected source occupies the first slot. The second slot remains
the original full field. Interchanging those slots is not a proof step.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment
open CommonResetGram CommonResetWeightedSources CommonResetWeightedSampling
open CommonResetGeneralReciprocity CommonResetGrid CollisionRampEnergy
open CommonResetDedekind EndpointReciprocityBridge
open DedekindReciprocity RademacherThreeTerm

def orderedBoundary (N q : ℕ) (b c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, Core.resetMass N b d *
    ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      weightedProfile N c ((a : ℝ)/d)*midpointRow q ((a : ℝ)/d)

theorem reset_mass_eq_weight (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    Core.resetMass N c d = resetWeight N c d := rfl

/-- The full ordered double sum, including the origin's zero row. -/
theorem ordered_boundary_coefficients (N q : ℕ) (b c : ℕ → ℝ) :
    orderedBoundary N q b c =
      2*∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        b d*c j*(arithmeticCoefficientDedekindTerm q j d : ℝ) := by
  have hzero : resetWeight N b 1 *
      (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j 1 : ℝ)) = 0 := by
    simp only [primitiveCorrelation_one, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
  calc
    orderedBoundary N q b c =
        ∑ d ∈ Finset.Icc 2 N, resetWeight N b d *
          (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j d : ℝ)) := by
      unfold orderedBoundary
      apply Finset.sum_congr rfl
      intro d hd
      rw [reset_mass_eq_weight, weighted_source_row (Finset.mem_Icc.mp hd).1]
    _ = ∑ d ∈ Finset.Icc 1 N, resetWeight N b d *
          (2*∑ j ∈ Finset.Icc 1 N, c j*(primitiveCoefficientCorrelation q j d : ℝ)) :=
      sum_Icc_remove_one N _ hzero
    _ = 2*∑ j ∈ Finset.Icc 1 N, c j *
          ∑ d ∈ Finset.Icc 1 N, resetWeight N b d*(primitiveCoefficientCorrelation q j d : ℝ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = 2*∑ j ∈ Finset.Icc 1 N, c j *
          ∑ d ∈ Finset.Icc 1 N, b d*(arithmeticCoefficientDedekindTerm q j d : ℝ) := by
      simp only [weighted_coefficient_columns]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro j _
      ring

def saturatedBoundary (N q Ω : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, if d ∣ Ω then
    Core.resetMass N c d *
      ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
        weightedProfile N c ((a : ℝ)/d)*midpointRow q ((a : ℝ)/d)
    else 0

/-- A reset selection changes its source slot, not its field slot. -/
theorem saturated_boundary_ordered (N q Ω : ℕ) (c : ℕ → ℝ) :
    saturatedBoundary N q Ω c = orderedBoundary N q (collapseSource N Ω c) c := by
  unfold saturatedBoundary orderedBoundary
  apply Finset.sum_congr rfl
  intro d _
  rw [collapse_reset_mass]
  split_ifs <;> simp

/-- The paper's A_sigma = 2 (P_sigma c)^T K c for saturated forests. -/
theorem saturated_boundary_coefficients (N q Ω : ℕ) (c : ℕ → ℝ) :
    saturatedBoundary N q Ω c =
      2*∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        collapseSource N Ω c d*c j*(arithmeticCoefficientDedekindTerm q j d : ℝ) := by
  rw [saturated_boundary_ordered, ordered_boundary_coefficients]

theorem prime_cutoff_coprime {p j : ℕ} (hp : p.Prime)
    (hj : j ∈ Finset.Icc 1 (p-1)) : j.Coprime (p^2) := by
  apply hp.coprime_pow_of_not_dvd
  intro hd
  have hpos := (Finset.mem_Icc.mp hj).1
  have hle := Nat.le_of_dvd hpos hd
  have hjp := (Finset.mem_Icc.mp hj).2
  have := hp.pos
  omega

theorem prime_cutoff_reset_mass {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    CommonResetWeightedSources.resetMass (p-1) (p^2) c =
      (∑ j ∈ Finset.Icc 1 (p-1), c j)^2 := by
  rw [resetMass_gcd_sum (pow_pos hp.pos 2)]
  have hentry (j : ℕ) (hj : j ∈ Finset.Icc 1 (p-1)) (k : ℕ) :
      (j.gcd k).gcd (p^2) = 1 :=
    ((prime_cutoff_coprime hp hj).of_dvd_left (Nat.gcd_dvd_left j k)).gcd_eq_one
  have hs :
      (∑ j ∈ Finset.Icc 1 (p-1), ∑ k ∈ Finset.Icc 1 (p-1),
        c j*c k*((j.gcd k).gcd (p^2) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (p-1), ∑ k ∈ Finset.Icc 1 (p-1), c j*c k := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_congr rfl (fun k _ => by simp [hentry j hj k])
  rw [hs, pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem prime_cutoff_curvature {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    curvatureMoment (p-1) (p^2) c =
      ∑ j ∈ Finset.Icc 1 (p-1), c j/(j : ℝ) := by
  apply Finset.sum_congr rfl
  intro j hj
  simp [(prime_cutoff_coprime hp hj).gcd_eq_one]

/-- The complete real-weight reset identity at the prime-square cutoff. -/
theorem weighted_prime_square_identity {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    weightedDefect (p-1) (p^2) c =
      ((∑ j ∈ Finset.Icc 1 (p-1), c j)^2 +
        4*weightedInterior (p-1) (p^2) c -
        (2*slopeMoment (p-1) c)*
          (∑ j ∈ Finset.Icc 1 (p-1), c j/(j : ℝ))/(3*(p : ℝ)^2)) /
        (p : ℝ)^2 := by
  rw [weighted_sampling_identity (pow_pos hp.pos 2), prime_cutoff_reset_mass hp,
    prime_cutoff_curvature hp]
  push_cast
  ring

end NField.ResetForests.Core
