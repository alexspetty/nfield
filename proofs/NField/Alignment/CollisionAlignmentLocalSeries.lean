/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResetLocalFactors

/-!
# Actual infinite alignment factors at one prime power

The numerator retains the infinite sum, including the exponent-zero
case for primes absent from the modulus. Splitting at the finite
valuation gives the reset prefix and an exactly summable geometric tail.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentLocalSeries

open scoped Classical
open Filter CollisionResetLocalFactors

def alignmentPrimeFactor (p : ℝ) (v : ℕ) : ℝ := 1+p⁻¹-(p⁻¹)^v/(p+1)

def alignmentPrimeTerm (p : ℝ) (v j : ℕ) : ℝ :=
  (1-p⁻¹)*(p⁻¹)^(2*(j+1)-min (j+1) v)*((j : ℝ)+1+(p-1)⁻¹)

def alignmentPrimeNumerator (p : ℝ) (v : ℕ) : ℝ := ∑' j : ℕ, alignmentPrimeTerm p v j

def alignmentPrimeAverage (p : ℝ) (v : ℕ) : ℝ := alignmentPrimeNumerator p v/alignmentPrimeFactor p v

theorem alignmentPrimeTerm_prefix (p : ℝ) {v j : ℕ} (hj : j < v) :
    alignmentPrimeTerm p v j=
      (1-p⁻¹)*(p⁻¹)^(j+1)*((j : ℝ)+1+(p-1)⁻¹) := by
  unfold alignmentPrimeTerm
  rw [min_eq_left (by omega : j+1 ≤ v)]
  rw [show 2*(j+1)-(j+1)=j+1 by omega]

theorem alignmentPrimeTerm_tail (p : ℝ) (v j : ℕ) :
    alignmentPrimeTerm p v (j+v)=
      (1-p⁻¹)*(p⁻¹)^(v+2)*
        (((v : ℝ)+1+(p-1)⁻¹)*((p⁻¹)^2)^j+(j : ℝ)*((p⁻¹)^2)^j) := by
  unfold alignmentPrimeTerm
  rw [min_eq_right (by omega : v ≤ j+v+1)]
  have he : 2*(j+v+1)-v=(v+2)+2*j := by omega
  rw [he,pow_add,pow_mul,Nat.cast_add]
  ring

theorem alignmentPrimeTerm_tail_hasSum {p : ℝ} (hp : 1 < p) (v : ℕ) :
    HasSum (fun j : ℕ => alignmentPrimeTerm p v (j+v))
      ((1-p⁻¹)*(p⁻¹)^(v+2)*
        (((v : ℝ)+1+(p-1)⁻¹)/(1-(p⁻¹)^2)+(p⁻¹)^2/(1-(p⁻¹)^2)^2)) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hq : ‖(p⁻¹)^2‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  have hg := hasSum_geometric_of_norm_lt_one hq
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have h := ((hg.mul_left ((v : ℝ)+1+(p-1)⁻¹)).add hn).mul_left ((1-p⁻¹)*(p⁻¹)^(v+2))
  simp_rw [alignmentPrimeTerm_tail]
  simpa only [div_eq_mul_inv] using h

theorem alignmentPrimeNumerator_hasSum {p : ℝ} (hp : 1 < p) (v : ℕ) :
    HasSum (alignmentPrimeTerm p v)
      (resetPrimeNumerator p v+(1-p⁻¹)*(p⁻¹)^(v+2)*
        (((v : ℝ)+1+(p-1)⁻¹)/(1-(p⁻¹)^2)+(p⁻¹)^2/(1-(p⁻¹)^2)^2)) := by
  have hpre : (∑ j ∈ Finset.range v, alignmentPrimeTerm p v j)=resetPrimeNumerator p v := by
    apply Finset.sum_congr rfl
    intro j hj
    exact alignmentPrimeTerm_prefix p (Finset.mem_range.mp hj)
  have h := (alignmentPrimeTerm_tail_hasSum hp v).sum_range_add
    (f := alignmentPrimeTerm p v) (k := v)
  rwa [hpre] at h

theorem alignmentPrimeNumerator_formula {p : ℝ} (hp : 1 < p) (v : ℕ) :
    alignmentPrimeNumerator p v=resetPrimeNumerator p v+(1-p⁻¹)*(p⁻¹)^(v+2)*
      (((v : ℝ)+1+(p-1)⁻¹)/(1-(p⁻¹)^2)+(p⁻¹)^2/(1-(p⁻¹)^2)^2) :=
  (alignmentPrimeNumerator_hasSum hp v).tsum_eq

theorem alignmentPrimeNumerator_nonneg {p : ℝ} (hp : 1 < p) (v : ℕ) :
    0 ≤ alignmentPrimeNumerator p v := by
  have hp0 : 0 < p := by linarith
  have hr1 : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp.le
  apply tsum_nonneg
  intro j
  unfold alignmentPrimeTerm
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) (by positivity)) (by positivity)

theorem alignmentPrimeNumerator_positive_indices {p : ℝ} (hp : 1 < p) (v : ℕ) :
    alignmentPrimeNumerator p v=
      ∑' j : ℕ, if 1 ≤ j then
        (1-1/p)/p^(2*j-min j v)*((j : ℝ)+1/(p-1)) else 0 := by
  let F : ℕ → ℝ := fun j => if 1 ≤ j then
    (1-1/p)/p^(2*j-min j v)*((j : ℝ)+1/(p-1)) else 0
  have he : (fun j : ℕ => F (j+1))=alignmentPrimeTerm p v := by
    funext j
    simp [F,alignmentPrimeTerm,div_eq_mul_inv,inv_pow]
  have hs : HasSum (fun j : ℕ => F (j+1)) (alignmentPrimeNumerator p v) := by
    rw [he]
    exact (alignmentPrimeNumerator_hasSum hp v).summable.hasSum
  have hzero : F 0=0 := by simp [F]
  have h := hs.zero_add
  rw [hzero,zero_add] at h
  exact h.tsum_eq.symm

theorem alignment_prime_local_factors {p : ℝ} (hp : 1 < p) (v : ℕ) :
    alignmentPrimeFactor p v=1+1/p-(1/p)^v/(p+1) ∧
      alignmentPrimeAverage p v=
        (∑' j : ℕ, if 1 ≤ j then
          (1-1/p)/p^(2*j-min j v)*((j : ℝ)+1/(p-1)) else 0)/alignmentPrimeFactor p v := by
  constructor
  · simp only [alignmentPrimeFactor,one_div]
  · rw [alignmentPrimeAverage,alignmentPrimeNumerator_positive_indices hp v]

end NField.Alignment.CollisionAlignmentLocalSeries
