/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentLocalBounds

/-!
# The local alignment factor is the sum of its arithmetic masses

The exponent-zero term is one. Positive exponents are split at the
valuation of the modulus; the remaining geometric series is proved
summable before its value is used. The prime specialization identifies
these masses with the paper's totient weights.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentPrimeMass

open scoped Classical
open CollisionResetLocalFactors CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds

def alignmentPrimeMass (p : ℝ) (v j : ℕ) : ℝ :=
  if j=0 then 1 else (1-p⁻¹)*(p⁻¹)^(2*j-min j v)

theorem resetPrimeFactor_mass_sum (p : ℝ) (v : ℕ) :
    resetPrimeFactor p v=1+∑ j ∈ Finset.range v, (1-p⁻¹)*(p⁻¹)^(j+1) := by
  induction v with
  | zero => simp [resetPrimeFactor]
  | succ v ih =>
    rw [resetPrimeFactor_succ,ih,Finset.sum_range_succ]
    ring

theorem alignmentPrimeMass_prefix (p : ℝ) (v : ℕ) :
    (∑ j ∈ Finset.range (v+1), alignmentPrimeMass p v j)=resetPrimeFactor p v := by
  rw [Finset.sum_range_succ',resetPrimeFactor_mass_sum]
  have he : (∑ j ∈ Finset.range v, alignmentPrimeMass p v (j+1))=
      ∑ j ∈ Finset.range v, (1-p⁻¹)*(p⁻¹)^(j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjv : j+1 ≤ v := by simpa using Finset.mem_range.mp hj
    simp only [alignmentPrimeMass,Nat.add_one_ne_zero,if_false,min_eq_left hjv]
    rw [show 2*(j+1)-(j+1)=j+1 by omega]
  rw [he]
  simp [alignmentPrimeMass,add_comm]

theorem alignmentPrimeMass_tail (p : ℝ) (v j : ℕ) :
    alignmentPrimeMass p v (j+(v+1))=
      (1-p⁻¹)*(p⁻¹)^(v+2)*((p⁻¹)^2)^j := by
  unfold alignmentPrimeMass
  rw [if_neg (by omega : j+(v+1) ≠ 0),min_eq_right (by omega : v ≤ j+(v+1))]
  rw [show 2*(j+(v+1))-v=(v+2)+2*j by omega,pow_add,pow_mul]
  ring

theorem alignmentPrimeMass_tail_hasSum {p : ℝ} (hp : 1 < p) (v : ℕ) :
    HasSum (fun j : ℕ => alignmentPrimeMass p v (j+(v+1)))
      ((1-p⁻¹)*(p⁻¹)^(v+2)/(1-(p⁻¹)^2)) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hq : ‖(p⁻¹)^2‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  simp_rw [alignmentPrimeMass_tail]
  simpa only [div_eq_mul_inv] using
    (hasSum_geometric_of_norm_lt_one hq).mul_left ((1-p⁻¹)*(p⁻¹)^(v+2))

theorem alignmentPrimeFactor_reset_tail {p : ℝ} (hp : 1 < p) (v : ℕ) :
    resetPrimeFactor p v+(1-p⁻¹)*(p⁻¹)^(v+2)/(1-(p⁻¹)^2)=
      alignmentPrimeFactor p v := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hpplus : p+1 ≠ 0 := ne_of_gt (by linarith)
  have he : 1-(p⁻¹)^2=(p-1)*(p+1)/p^2 := by
    field_simp
    ring
  unfold resetPrimeFactor alignmentPrimeFactor
  rw [he]
  simp only [pow_add,pow_one]
  field_simp
  ring

theorem alignmentPrimeMass_hasSum {p : ℝ} (hp : 1 < p) (v : ℕ) :
    HasSum (alignmentPrimeMass p v) (alignmentPrimeFactor p v) := by
  have h := (alignmentPrimeMass_tail_hasSum hp v).sum_range_add
    (f := alignmentPrimeMass p v) (k := v+1)
  rwa [alignmentPrimeMass_prefix,alignmentPrimeFactor_reset_tail hp v] at h

theorem alignmentPrimeMass_totient {p : ℕ} (hp : p.Prime) (v j : ℕ) :
    alignmentPrimeMass (p : ℝ) v j=
      (Nat.totient (p^j) : ℝ)*(p : ℝ)^(min j v)/(p : ℝ)^(3*j) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  cases j with
  | zero => simp [alignmentPrimeMass]
  | succ j =>
    have hphi : (Nat.totient (p^(j+1)) : ℝ)=(p : ℝ)^(j+1)*(1-(p : ℝ)⁻¹) := by
      rw [Nat.totient_prime_pow_succ hp,Nat.cast_mul,Nat.cast_pow,
        Nat.cast_sub hp.one_le,Nat.cast_one,pow_succ]
      field_simp
    change alignmentPrimeMass (p : ℝ) v (j+1)=_
    rw [hphi]
    simp only [alignmentPrimeMass,Nat.add_one_ne_zero,if_false,inv_pow]
    have hmin : min (j+1) v ≤ 2*(j+1) := (min_le_left _ _).trans (by omega)
    rw [pow_sub₀ (p : ℝ) hp0 hmin]
    rw [show 3*(j+1)=(j+1)+2*(j+1) by omega,pow_add]
    field_simp
    ring

theorem alignment_prime_arithmetic_factor {p : ℕ} (hp : p.Prime) (v : ℕ) :
    HasSum (fun j : ℕ =>
      (Nat.totient (p^j) : ℝ)*(p : ℝ)^(min j v)/(p : ℝ)^(3*j))
      (alignmentPrimeFactor (p : ℝ) v) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have h : HasSum (fun j : ℕ => alignmentPrimeMass (p : ℝ) v j)
      (alignmentPrimeFactor (p : ℝ) v) := alignmentPrimeMass_hasSum hp1 v
  simpa only [alignmentPrimeMass_totient hp] using h

end NField.Alignment.CollisionAlignmentPrimeMass
