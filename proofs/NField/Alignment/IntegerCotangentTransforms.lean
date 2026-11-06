/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CotangentGrid
import NField.Alignment.IntegerInverseSeriesLiteral
import NField.Alignment.IntegerDedekindTransform

/-! # The cotangent steps retain signed numerators and signed Fourier frequencies -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerCotangentTransforms
open scoped BigOperators Classical
open CotangentGrid IntegerInverseResidue IntegerInverseSeriesLiteral IntegerDedekindTransform
  DedekindInverseResidueTransform CollisionDedekindPairing

def integerCotangentSum (q : ℕ) (r : ℤ) : ℂ :=
  ∑ u ∈ Finset.Ico 1 q,(cotGrid q u : ℂ)*integerInverseCoefficient q r u

theorem integer_cotangent_nat (q r : ℕ) :
    integerCotangentSum q (r : ℤ)=finiteInverseCotangentSum q r := by
  unfold integerCotangentSum finiteInverseCotangentSum
  apply Finset.sum_congr rfl
  intro u hu
  rw [integer_coefficient_nat]
  congr 1
  unfold cotGrid
  rw [Complex.ofReal_cot]
  congr 1
  push_cast
  ring

theorem integer_cotangent_neg (q : ℕ) (r : ℤ) :
    integerCotangentSum q (-r)= -integerCotangentSum q r := by
  unfold integerCotangentSum
  simp only [integer_coefficient_neg,mul_neg,Finset.sum_neg_distrib]

/-- Title: `The inverse series equals the cotangent sum for every signed numerator`. -/
theorem integer_series_cotangent {q : ℕ} (hq : 2 ≤ q) (r : ℤ) :
    integerInverseSeries q r=(Real.pi : ℂ)/(2*(q : ℂ))*integerCotangentSum q r := by
  cases r with
  | ofNat r =>
      change integerInverseSeries q (r : ℤ)=(Real.pi : ℂ)/(2*(q : ℂ))*integerCotangentSum q (r : ℤ)
      rw [integer_series_nat,integer_cotangent_nat]
      exact inverseSawSeries_eq_cotangent_sum hq
  | negSucc r =>
      change integerInverseSeries q (-((r+1 : ℕ) : ℤ))=
        (Real.pi : ℂ)/(2*(q : ℂ))*integerCotangentSum q (-((r+1 : ℕ) : ℤ))
      rw [integer_series_neg,integer_cotangent_neg,integer_series_nat,integer_cotangent_nat,
        inverseSawSeries_eq_cotangent_sum hq,mul_neg]

theorem integer_cotangent_literal {q : ℕ} (hq : 0 < q) (r : ℤ) :
    integerCotangentSum q r=
      ∑ u ∈ (Finset.Ico 1 q).filter (fun u => u.Coprime q),
        (cotGrid q u : ℂ)*
          (periodicSawtooth ((r : ℝ)*(inverseResidue u q : ℝ)/(q : ℝ)) : ℂ) := by
  unfold integerCotangentSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hcop : u.Coprime q
  · rw [if_pos hcop,integer_inverse_coefficient_literal hq hcop]
  · simp [hcop,integerInverseCoefficient,hq.ne']

/-- Title: `The literal cotangent and inverse-sawtooth sum`. -/
theorem integer_inverse_cotangent_identity {q : ℕ} (hq : 2 ≤ q) (r : ℤ) :
    (∑ u ∈ (Finset.Ico 1 q).filter (fun u => u.Coprime q),
      (cotGrid q u : ℂ)*
        (periodicSawtooth ((r : ℝ)*(inverseResidue u q : ℝ)/(q : ℝ)) : ℂ))=
      (2*(q : ℂ)/(Real.pi : ℂ))*integerInverseSeries q r := by
  rw [← integer_cotangent_literal (by omega),integer_series_cotangent hq]
  have hqC : (q : ℂ)≠0 := by exact_mod_cast (show q≠0 by omega)
  have hπ : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem cotangent_transform_factor {K g : ℕ} (hK : 0 < K) (hg : g∣K) (hg0 : 0 < g) :
    (K : ℂ)*(-(1/((Real.pi : ℂ)*Complex.I)))*
      ((1/(g : ℂ))*((Real.pi : ℂ)/(2*((K/g : ℕ) : ℂ))))=Complex.I/2 := by
  have hKc : (K : ℂ)≠0 := by exact_mod_cast hK.ne'
  have hgc : (g : ℂ)≠0 := by exact_mod_cast hg0.ne'
  have hq : 0 < K/g := Nat.div_pos (Nat.le_of_dvd hK hg) hg0
  have hqc : ((K/g : ℕ) : ℂ)≠0 := by exact_mod_cast hq.ne'
  have hπ : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hfac : (g : ℂ)*((K/g : ℕ) : ℂ)=(K : ℂ) := by exact_mod_cast Nat.mul_div_cancel' hg
  field_simp [Complex.I_ne_zero]
  simp only [Complex.I_sq]
  linear_combination hfac

/-- Title: `The full cotangent transform at every integer frequency`. -/
theorem integer_full_cotangent {K : ℕ} (hK : 2 ≤ K) (t : ℤ) :
    integerFullTransform K t=Complex.I/2*
      ∑ g ∈ (Int.gcd (K : ℤ) t).divisors.filter (fun g => 2 ≤ K/g),
        integerCotangentSum (K/g) (t/(g : ℤ)) := by
  have hKc : (K : ℂ)≠0 := by exact_mod_cast (show K≠0 by omega)
  have he := integer_additive_transform hK t
  have h := congrArg (fun z : ℂ => (K : ℂ)*z) he
  rw [mul_div_cancel₀ _ hKc] at h
  rw [h,integerFullSeriesSide,← mul_assoc,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hq := (Finset.mem_filter.mp hg).2
  have hgd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hg).1
  have hgK : g∣K := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs,Int.natAbs_natCast] at hgd
    exact hgd.trans (Nat.gcd_dvd_left K t.natAbs)
  have hg0 := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg).1
  rw [integer_series_cotangent hq]
  calc
    _ = ((K : ℂ)*(-(1/((Real.pi : ℂ)*Complex.I)))*
        ((1/(g : ℂ))*((Real.pi : ℂ)/(2*((K/g : ℕ) : ℂ)))))*
          integerCotangentSum (K/g) (t/(g : ℤ)) := by ring
    _ = _ := by rw [cotangent_transform_factor (by omega) hgK hg0]

end NField.Alignment.IntegerCotangentTransforms
