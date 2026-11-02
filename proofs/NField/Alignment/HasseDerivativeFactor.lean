/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic

/-!
# The Hasse derivative factor in Stepanov's construction

The derivative of order k of g*f^n is divisible by f^(n-k), in every
characteristic. For nonzero f over an integral domain the quotient is unique
and depends linearly on g. This is the algebraic step in Harcos, Lemma 10;
it is not a point-count or Kloosterman estimate.
-/

set_option autoImplicit false
namespace NField.Alignment.HasseDerivativeFactor

open scoped BigOperators
open Polynomial

/-- All characteristics, with natural subtraction also covering k>=n. -/
theorem pow_dvd_hasse_mul_pow {R : Type*} [CommSemiring R]
    (f g : R[X]) (n k : ℕ) : f ^ (n - k) ∣ hasseDeriv k (g * f ^ n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    by_cases hnk : n + 1 ≤ k
    · simp [Nat.sub_eq_zero_of_le hnk]
    have hk : k ≤ n := by omega
    rw [pow_succ, ← mul_assoc, hasseDeriv_mul]
    apply Finset.dvd_sum
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    by_cases hj : ij.2 = 0
    · have hi : ij.1 = k := by omega
      obtain ⟨Q, hQ⟩ := ih k
      simp only [hi, hj, hasseDeriv_zero, LinearMap.id_apply]
      refine ⟨Q, ?_⟩
      rw [hQ, show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    · apply dvd_trans (pow_dvd_pow f (show n + 1 - k ≤ n - ij.1 by omega))
      exact (ih ij.1).mul_right _

/-- The unique factor for a nonzero base polynomial is a linear function
of g. No factorial division is used. -/
noncomputable def quotientMap {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hf : f ≠ 0) (n k : ℕ) : R[X] →ₗ[R] R[X] := by
  classical
  let Q : R[X] → R[X] := fun g => (pow_dvd_hasse_mul_pow f g n k).choose
  have hQ (g : R[X]) : hasseDeriv k (g * f ^ n) = f ^ (n-k) * Q g :=
    (pow_dvd_hasse_mul_pow f g n k).choose_spec
  refine { toFun := Q, map_add' := ?_, map_smul' := ?_ }
  · intro g h
    apply mul_left_cancel₀ (pow_ne_zero (n-k) hf)
    rw [mul_add, ← hQ, ← hQ, ← hQ, add_mul, map_add]
  · intro c g
    apply mul_left_cancel₀ (pow_ne_zero (n-k) hf)
    change f ^ (n-k) * Q (c • g) = f ^ (n-k) * (c • Q g)
    rw [mul_smul_comm, ← hQ, ← hQ, smul_mul_assoc, map_smul]

/-- The literal quotient-factor identity. -/
theorem hasse_mul_pow_factor {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hf : f ≠ 0) (g : R[X]) (n k : ℕ) :
    hasseDeriv k (g * f ^ n) = f ^ (n-k) * quotientMap f hf n k g :=
  (pow_dvd_hasse_mul_pow f g n k).choose_spec

/-- Natural-degree bound, with truncated subtraction valid even for zero
quotient or constant f. For positive-degree f the subtraction is exact. -/
theorem quotient_natDegree_le {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hf : f ≠ 0) (g : R[X]) {n k : ℕ} (hk : k ≤ n) :
    (quotientMap f hf n k g).natDegree ≤ g.natDegree + k * f.natDegree - k := by
  by_cases hg : g = 0
  · subst g
    simp
  by_cases hQ : quotientMap f hf n k g = 0
  · rw [hQ]
    simp
  have hbound := natDegree_hasseDeriv_le (g * f ^ n) k
  rw [hasse_mul_pow_factor f hf g n k,
    natDegree_mul (pow_ne_zero (n-k) hf) hQ,
    natDegree_mul hg (pow_ne_zero n hf), natDegree_pow, natDegree_pow] at hbound
  have hexp : (n-k) * f.natDegree + k * f.natDegree = n * f.natDegree := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hk]
  omega

/-- The literal degree bound of the auxiliary-polynomial construction for
positive-degree f, avoiding any negative-degree convention for zero. -/
theorem quotient_natDegree_add_order_le {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree) (g : R[X])
    {n k : ℕ} (hk : k ≤ n) :
    (quotientMap f hf n k g).natDegree + k ≤ g.natDegree + k * f.natDegree := by
  have h := quotient_natDegree_le f hf g hk
  have hkd : k ≤ k * f.natDegree := by nlinarith
  omega

/-- Lemma 10 as one reusable package: a linear quotient map, exact
factorization for every g, and the degree estimate needed by Stepanov. -/
theorem hasse_factor_linear_degree {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hdeg : 1 ≤ f.natDegree) {n k : ℕ} (hk : k ≤ n) :
    ∃ Q : R[X] →ₗ[R] R[X], ∀ g : R[X],
      hasseDeriv k (g * f ^ n) = Q g * f ^ (n-k) ∧
      (Q g).natDegree + k ≤ g.natDegree + k * f.natDegree := by
  have hf : f ≠ 0 := by intro h; simp [h] at hdeg
  refine ⟨quotientMap f hf n k, ?_⟩
  intro g
  exact ⟨by rw [hasse_mul_pow_factor f hf g n k, mul_comm],
    quotient_natDegree_add_order_le f hf hdeg g hk⟩

end NField.Alignment.HasseDerivativeFactor
