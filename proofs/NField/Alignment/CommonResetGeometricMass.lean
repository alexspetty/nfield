/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSmallConductors

/-! # The full centered geometric mass -/

noncomputable section

namespace NField.Alignment.CommonResetGeometricMass

open scoped BigOperators
open CommonResetSmallConductors

theorem sum_symmetric_Icc (R : ℕ) (f : ℤ → ℝ) (hzero : f 0 = 0)
    (hneg : ∀ z, f (-z) = f z) :
    (∑ z ∈ Finset.Icc (-(R : ℤ)) R, f z) =
      2*∑ n ∈ Finset.Icc 1 R, f (n : ℤ) := by
  classical
  let P := (Finset.Icc 1 R).image (fun n : ℕ => (n : ℤ))
  let M := (Finset.Icc 1 R).image (fun n : ℕ => -(n : ℤ))
  have hP (z : ℤ) : z ∈ P ↔ 1 ≤ z ∧ z ≤ R := by
    simp only [P, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact_mod_cast hn
    · intro hz
      refine ⟨z.toNat, ?_, Int.toNat_of_nonneg (by omega)⟩
      omega
  have hM (z : ℤ) : z ∈ M ↔ -(R : ℤ) ≤ z ∧ z ≤ -1 := by
    simp only [M, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨n, hn, rfl⟩
      constructor <;> omega
    · intro hz
      refine ⟨(-z).toNat, ?_, ?_⟩
      · omega
      · rw [Int.toNat_of_nonneg (by omega)]
        omega
  have hset : Finset.Icc (-(R : ℤ)) R = insert 0 (P ∪ M) := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, hP, hM]
    omega
  have hnot : (0 : ℤ) ∉ P ∪ M := by simp only [Finset.mem_union, hP, hM]; omega
  have hdisj : Disjoint P M := by
    rw [Finset.disjoint_left]
    intro z hzP hzM
    have hp := (hP z).mp hzP
    have hm := (hM z).mp hzM
    omega
  rw [hset, Finset.sum_insert hnot, hzero, zero_add, Finset.sum_union hdisj]
  have hsumP : (∑ z ∈ P, f z) = ∑ n ∈ Finset.Icc 1 R, f (n : ℤ) := by
    dsimp only [P]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Int.ofNat_injective hab
  have hsumM : (∑ z ∈ M, f z) = ∑ n ∈ Finset.Icc 1 R, f (n : ℤ) := by
    dsimp only [M]
    rw [Finset.sum_image]
    · simp only [hneg]
    · intro a _ b _ hab
      exact Int.ofNat_injective (neg_injective hab)
  rw [hsumP, hsumM]
  ring

def geometricMassTerm (p M : ℕ) (z : ℤ) : ℝ :=
  if z = 0 then 0 else min (M : ℝ) ((p : ℝ)/|(z : ℝ)|)

/-- Title: `The centered geometric mass has its complete harmonic bound`. -/
theorem centered_geometric_mass (p M R : ℕ) :
    (∑ z ∈ Finset.Icc (-(R : ℤ)) R, geometricMassTerm p M z) ≤
      2*(p : ℝ)*(harmonic R : ℝ) := by
  rw [sum_symmetric_Icc R _ (by simp [geometricMassTerm])
    (fun z => by simp [geometricMassTerm, abs_neg])]
  have hsum : (∑ n ∈ Finset.Icc 1 R, geometricMassTerm p M (n : ℤ)) ≤
      (p : ℝ)*(harmonic R : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 R, (p : ℝ)/(n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have h := Finset.mem_Icc.mp hn; omega)
        rw [geometricMassTerm, if_neg hn0]
        simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using
          min_le_right (M : ℝ) ((p : ℝ)/|(n : ℝ)|)
      _ = _ := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [Finset.mul_sum, div_eq_mul_inv]
  nlinarith

/-- Title: `The half-carrier geometric mass is uniformly logarithmic`. -/
theorem half_carrier_geometric_mass (p M : ℕ) :
    (∑ z ∈ Finset.Icc (-((p/2 : ℕ) : ℤ)) (p/2 : ℕ), geometricMassTerm p M z) ≤
      2*(p : ℝ)*(harmonic p : ℝ) := by
  exact (centered_geometric_mass p M (p/2)).trans
    (mul_le_mul_of_nonneg_left (harmonic_monotone (Nat.div_le_self p 2)) (by positivity))

end NField.Alignment.CommonResetGeometricMass
