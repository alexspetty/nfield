/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSampling

/-! # The entire interior source as a Dedekind double sum -/

noncomputable section

namespace NField.Alignment.CommonResetDedekind

open scoped BigOperators
open CommonResetSampling CommonResetGrid CollisionRampEnergy
open EndpointReciprocityBridge DedekindReciprocity RademacherThreeTerm

theorem sum_divisor_columns (N : ℕ) (f : ℕ → ℚ) :
    (∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, f d) =
      ∑ d ∈ Finset.Icc 1 N, ((N/d : ℕ) : ℚ)*f d := by
  classical
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ k then f d else 0 := by
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
      rw [hset, Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, if d ∣ k then f d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hinterval]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]

theorem coefficient_columns (N q j : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, arithmeticCoefficientDedekindTerm q j k) =
      ∑ d ∈ Finset.Icc 1 N, ((N/d : ℕ) : ℚ)*primitiveCoefficientCorrelation q j d := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors,
        primitiveCoefficientCorrelation q j d := by
      apply Finset.sum_congr rfl
      intro k hk
      exact arithmeticCoefficientDedekindTerm_eq_primitiveDivisorSum (Finset.mem_Icc.mp hk).1
    _ = _ := sum_divisor_columns _ _

theorem primitiveCorrelation_one (q j : ℕ) : primitiveCoefficientCorrelation q j 1 = 0 := by
  simp [primitiveCoefficientCorrelation, rationalSawtooth]

theorem sum_Icc_remove_one (N : ℕ) (f : ℕ → ℝ) (h1 : f 1 = 0) :
    (∑ d ∈ Finset.Icc 2 N, f d) = ∑ d ∈ Finset.Icc 1 N, f d := by
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d hd hnot
    have h : d = 1 := by
      simp only [Finset.mem_Icc] at hd hnot
      omega
    simpa [h] using h1

theorem source_row {d : ℕ} (hd : 2 ≤ d) (N q : ℕ) :
    (∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
      boundaryResponse N ((a : ℝ)/(d : ℝ))*midpointRow q ((a : ℝ)/(d : ℝ))) =
      2 * ∑ j ∈ Finset.Icc 1 N, (primitiveCoefficientCorrelation q j d : ℝ) := by
  have hdpos : 0 < d := by omega
  unfold boundaryResponse
  simp only [Finset.mul_sum, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← BernoulliCurvature.reducedResidues_eq_Ico hd]
  unfold primitiveCoefficientCorrelation
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [midpointRow_rational hdpos, midpointRow_rational hdpos]
  ring

/-- Title: `Every reset contributes to the full coefficient double sum`. -/
theorem interiorSource_coefficient_sum (N q : ℕ) :
    interiorSource N q =
      2 * ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        (arithmeticCoefficientDedekindTerm q j k : ℝ) := by
  have hcolumns (j : ℕ) :
      (∑ k ∈ Finset.Icc 1 N, (arithmeticCoefficientDedekindTerm q j k : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N,
          ((N/d : ℕ) : ℝ)*(primitiveCoefficientCorrelation q j d : ℝ) := by
    exact_mod_cast coefficient_columns N q j
  rw [Finset.sum_comm]
  simp only [hcolumns]
  rw [Finset.sum_comm]
  unfold interiorSource
  simp only [← Finset.mul_sum]
  have hzero : ((N/1 : ℕ) : ℝ)*
      (2 * ∑ j ∈ Finset.Icc 1 N, (primitiveCoefficientCorrelation q j 1 : ℝ)) = 0 := by
    simp only [primitiveCorrelation_one, Rat.cast_zero, Finset.sum_const_zero, mul_zero]
  calc
    _ = ∑ d ∈ Finset.Icc 2 N,
        ((N/d : ℕ) : ℝ)*(2 * ∑ j ∈ Finset.Icc 1 N,
          (primitiveCoefficientCorrelation q j d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [source_row (Finset.mem_Icc.mp hd).1]
    _ = ∑ d ∈ Finset.Icc 1 N,
        ((N/d : ℕ) : ℝ)*(2 * ∑ j ∈ Finset.Icc 1 N,
          (primitiveCoefficientCorrelation q j d : ℝ)) := sum_Icc_remove_one _ _ hzero
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

def inverseDedekindTerm (q j k : ℕ) : ℚ :=
  if h : q.Coprime k then
    arithmeticDedekindSum ((ZMod.unitOfCoprime q h)⁻¹.val.val * j) k
  else 0

/-- Title: `The interior source is the complete Dedekind double sum`. -/
theorem dedekind_representation (N q : ℕ)
    (hq : ∀ k ∈ Finset.Icc 1 N, q.Coprime k) :
    interiorSource N q =
      2 * ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        (inverseDedekindTerm q j k : ℝ) := by
  rw [interiorSource_coefficient_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j _
  rw [inverseDedekindTerm, dif_pos (hq k hk),
    arithmeticCoefficientDedekindTerm_unit_left (Finset.mem_Icc.mp hk).1 (hq k hk)]

end NField.Alignment.CommonResetDedekind
