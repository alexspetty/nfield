/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionUniformAmplitude

/-!
# Elementary uniform bounds for the spectral error

A telescoping product bounds Delta uniformly below. The literal amplitude
error product then gives an inverse-square bound sufficient for the
lower-order spectral tails. This is not the stronger divisor-growth bound
mentioned in the manuscript's written argument.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralErrorBound

open scoped BigOperators Classical
open CollisionAmplitudeArithmetic CollisionHarmonicSeed CollisionZetaMoments
open CollisionConductorArithmetic CollisionJordanVariance CollisionUniformAmplitude

def squareEulerFactor (n : ℕ) : ℝ := 1-((n : ℝ)^2)⁻¹

theorem squareEulerFactor_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ squareEulerFactor n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hsq)

theorem squareEulerFactor_le_one (n : ℕ) : squareEulerFactor n ≤ 1 :=
  sub_le_self _ (inv_nonneg.mpr (sq_nonneg _))

theorem squareEulerFactor_le_cube {n : ℕ} (hn : 2 ≤ n) :
    squareEulerFactor n ≤ 1-((n : ℝ)^3)⁻¹ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hpow : (n : ℝ)^2 ≤ (n : ℝ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (by linarith : 0 ≤ (n : ℝ)-1)]
  exact sub_le_sub_left ((inv_le_inv₀ (pow_pos hnp 3) (sq_pos_of_pos hnp)).mpr hpow) 1

theorem consecutive_square_product (N : ℕ) :
    (∏ n ∈ Finset.Icc 2 (N+1), squareEulerFactor n)=
      ((N : ℝ)+2)/(2*((N : ℝ)+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ N+1+1),ih]
      simp only [squareEulerFactor,Nat.cast_add,Nat.cast_one]
      have h1 : (N : ℝ)+1≠0 := by positivity
      have h2 : (N : ℝ)+1+1≠0 := by positivity
      field_simp
      ring

theorem consecutive_square_product_lower (N : ℕ) :
    (1/2 : ℝ) ≤ ∏ n ∈ Finset.Icc 2 (N+1), squareEulerFactor n := by
  rw [consecutive_square_product]
  apply (le_div_iff₀ (by positivity : 0 < 2*((N : ℝ)+1))).mpr
  linarith

theorem deltaThree_uniform_lower (q : ℕ) : (1/2 : ℝ) ≤ deltaThree q := by
  by_cases hq : q=0
  · norm_num [hq,deltaThree]
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have hsub : (N+1).primeFactors ⊆ Finset.Icc 2 (N+1) := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      Nat.le_of_dvd (Nat.succ_pos N) (Nat.dvd_of_mem_primeFactors hp)⟩
  calc
    (1/2 : ℝ) ≤ ∏ n ∈ Finset.Icc 2 (N+1), squareEulerFactor n :=
      consecutive_square_product_lower N
    _ ≤ ∏ p ∈ (N+1).primeFactors, squareEulerFactor p :=
      Finset.prod_le_prod_of_subset_of_le_one hsub
        (fun n hn => squareEulerFactor_nonneg (Finset.mem_Icc.mp hn).1)
        (fun n _ _ => squareEulerFactor_le_one n)
    _ ≤ deltaThree (N+1) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact squareEulerFactor_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
      · intro p hp
        exact squareEulerFactor_le_cube (Nat.prime_of_mem_primeFactors hp).two_le

theorem prime_plus_one_product_bound {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, ((p : ℝ)+1)) ≤ (q : ℝ)^2 := by
  have hrad : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq q.prod_primeFactors_dvd
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ)^2 := by
      apply Finset.prod_le_prod
      · intro p _
        positivity
      · intro p hp
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        nlinarith
    _ = (∏ p ∈ q.primeFactors, (p : ℝ))^2 := by rw [Finset.prod_pow]
    _ ≤ _ := pow_le_pow_left₀ (Finset.prod_nonneg (fun n _ => Nat.cast_nonneg n)) hrad 2

def coarseErrorFactor : ℝ := zetaNat 4/(6*zetaThree)

theorem coarseErrorFactor_pos : 0 < coarseErrorFactor := by
  unfold coarseErrorFactor
  positivity [zetaNat_pos (by norm_num : 1<(4 : ℕ)),zetaThree_pos]

theorem amplitude_error_inverse_square {q : ℕ} (hq : 0 < q) :
    |amplitudeError q| ≤ coarseErrorFactor/(q : ℝ)^2 := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hz : zetaThree≠0 := zetaThree_pos.ne'
  have hd : deltaThree q≠0 := (deltaThree_pos q).ne'
  have hdinv : 1/deltaThree q ≤ 2 := by
    apply (div_le_iff₀ (deltaThree_pos q)).mpr
    linarith [deltaThree_uniform_lower q]
  calc
    _ ≤ zetaNat 4/(12*zetaThree*(q : ℝ)^4*deltaThree q)*
        ∏ p ∈ q.primeFactors, ((p : ℝ)+1) := amplitude_uniform_error hq
    _ ≤ zetaNat 4/(12*zetaThree*(q : ℝ)^4*deltaThree q)*(q : ℝ)^2 :=
      mul_le_mul_of_nonneg_left (prime_plus_one_product_bound hq)
        (by positivity [zetaNat_pos (by norm_num : 1<(4 : ℕ)),zetaThree_pos,deltaThree_pos q])
    _ ≤ coarseErrorFactor/(q : ℝ)^2 := by
      have h := mul_le_mul_of_nonneg_left hdinv
        (by positivity [zetaNat_pos (by norm_num : 1<(4 : ℕ)),zetaThree_pos] :
          0 ≤ zetaNat 4/(12*zetaThree*(q : ℝ)^2))
      convert! h using 1
      · field_simp
      · unfold coarseErrorFactor
        field_simp
        ring

theorem rho_nonneg {q : ℕ} (hq : 0 < q) : 0 ≤ rho q := by
  rw [rho_euler_product hq.ne']
  apply Finset.prod_nonneg
  intro p _
  positivity

theorem rho_le_one {q : ℕ} (hq : 0 < q) : rho q ≤ 1 := by
  rw [rho_euler_product hq.ne']
  apply Finset.prod_le_one
  · intro p _
    positivity
  · intro p _
    apply (div_le_one (by positivity : 0 < (p : ℝ)^2+p+1)).mpr
    have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith

theorem jordanTwo_le_square {q : ℕ} (hq : 0 < q) : jordanTwo q ≤ (q : ℝ)^2 := by
  rw [jordanTwo_euler_product hq.ne']
  have hprod : (∏ p ∈ q.primeFactors, squareEulerFactor p) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact squareEulerFactor_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
    · intro p _
      exact squareEulerFactor_le_one p
  have h := mul_le_mul_of_nonneg_left hprod (sq_nonneg (q : ℝ))
  simpa only [squareEulerFactor,mul_one] using h

end NField.Alignment.CollisionSpectralErrorBound
