/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovAuxiliary

/-! # Degree bounds for Stepanov's auxiliary polynomial and constraints -/

set_option autoImplicit false
namespace NField.Alignment.StepanovAuxiliaryDegree

open scoped BigOperators
open Polynomial HasseDerivativeFactor StepanovAuxiliary

/-- A uniform coefficient-degree bound controls the actual auxiliary
polynomial, including an empty coefficient family. -/
theorem auxiliary_natDegree_le {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (r s : ℕ → K[X]) (ell d J R : ℕ)
    (hr : ∀ j < J, (r j).natDegree ≤ R)
    (hs : ∀ j < J, (s j).natDegree ≤ R) :
    (auxiliary f r s ell d J).natDegree ≤
      R + (ell+d) * f.natDegree + (J-1) * Fintype.card K := by
  unfold auxiliary
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjJ := Finset.mem_range.mp hj
  calc
    _ ≤ (r j * f ^ ell + s j * f ^ (ell+d)).natDegree +
        (X ^ (j * Fintype.card K) : K[X]).natDegree := natDegree_mul_le
    _ ≤ max ((r j).natDegree + ell * f.natDegree)
        ((s j).natDegree + (ell+d) * f.natDegree) + j * Fintype.card K := by
      simp only [natDegree_X_pow]
      gcongr
      apply natDegree_add_le_of_degree_le
      · have h := natDegree_mul_le (p := r j) (q := f^ell)
        simp only [natDegree_pow] at h
        exact h.trans (le_max_left _ _)
      · have h := natDegree_mul_le (p := s j) (q := f^(ell+d))
        simp only [natDegree_pow] at h
        exact h.trans (le_max_right _ _)
    _ ≤ _ := by
      apply Nat.add_le_add
      · apply max_le
        · have := hr j hjJ
          nlinarith
        · exact Nat.add_le_add_right (hs j hjJ) _
      · exact Nat.mul_le_mul_right _ (by omega)

/-- The polynomial whose vanishing enforces the k-th derivative condition
on points with f(a)^d equal to the selected value. -/
noncomputable def constraint {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (r s : ℕ → K[X])
    (ell d J k : ℕ) (value : K) : K[X] :=
  ∑ j ∈ Finset.range J,
    (quotientMap f hf ell k (r j) + C value * quotientMap f hf (ell+d) k (s j)) * X^j

/-- The constraint degree grows by k*(deg f-1), independently of d.
This is the bound needed to count scalar linear equations. -/
theorem constraint_natDegree_le {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (r s : ℕ → K[X]) (ell d J k R : ℕ) (value : K) (hk : k ≤ ell)
    (hr : ∀ j < J, (r j).natDegree ≤ R)
    (hs : ∀ j < J, (s j).natDegree ≤ R) :
    (constraint f hf r s ell d J k value).natDegree ≤
      R + k * (f.natDegree-1) + (J-1) := by
  have hQ (g : K[X]) (n : ℕ) (hkn : k ≤ n) (hg : g.natDegree ≤ R) :
      (quotientMap f hf n k g).natDegree ≤ R + k * (f.natDegree-1) := by
    have h := quotient_natDegree_add_order_le f hf hdeg g hkn
    have hm : f.natDegree-1+1 = f.natDegree := by omega
    nlinarith
  unfold constraint
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjJ := Finset.mem_range.mp hj
  calc
    _ ≤ (quotientMap f hf ell k (r j) + C value *
        quotientMap f hf (ell+d) k (s j)).natDegree + j := by
      simpa only [natDegree_X_pow] using (natDegree_mul_le
        (p := quotientMap f hf ell k (r j) + C value * quotientMap f hf (ell+d) k (s j))
        (q := (X : K[X])^j))
    _ ≤ (R + k * (f.natDegree-1)) + (J-1) := by
      apply Nat.add_le_add _ (by omega)
      apply natDegree_add_le_of_degree_le
      · exact hQ (r j) ell hk (hr j hjJ)
      · exact (natDegree_C_mul_le _ _).trans (hQ (s j) (ell+d) (by omega) (hs j hjJ))

end NField.Alignment.StepanovAuxiliaryDegree
