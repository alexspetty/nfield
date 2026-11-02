/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothDivisor

/-!
# Reciprocal mass with selected primes forbidden

Reuse the finite geometric Euler product for an arbitrary allowed prime
set. Removing S from the primes up to Q multiplies the full inverse prime
product by the factors 1-1/p, hence costs at most exp(-sum_{p in S} 1/p).
No squarefree restriction or factorial counting is needed for this bound.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevAllowedEulerProduct
open scoped BigOperators Topology Classical
open Filter CollisionMertensInput HarperSmoothDivisor

def inverseProduct (A : Finset ℕ) : ℝ := ∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹

theorem factored_reciprocal_hasSum (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers A => ((n : ℕ) : ℝ)⁻¹) (inverseProduct A) := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun {_} hp => hprime hp) A).2
  have hf : A.filter Nat.Prime = A := Finset.filter_true_of_mem hA
  simpa only [hf, reciprocalHom, MonoidHom.coe_mk, OneHom.coe_mk, inverseProduct] using h

theorem factored_partial_reciprocal_bound (A W : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hW : ∀ w ∈ W, w ∈ Nat.factoredNumbers A) :
    (∑ w ∈ W, (1 : ℝ) / w) ≤ inverseProduct A := by
  have h := factored_reciprocal_hasSum A hA
  have hs : Summable ((Nat.factoredNumbers A).indicator (fun n : ℕ => (n : ℝ)⁻¹)) :=
    (summable_subtype_iff_indicator (s := Nat.factoredNumbers A)
      (f := fun n : ℕ => (n : ℝ)⁻¹)).mp h.summable
  have he : (∑' n : ℕ, (Nat.factoredNumbers A).indicator (fun d : ℕ => (d : ℝ)⁻¹) n) =
      inverseProduct A :=
    (tsum_subtype (Nat.factoredNumbers A) (fun n : ℕ => (n : ℝ)⁻¹)).symm.trans h.tsum_eq
  rw [← he]
  have hb := hs.sum_le_tsum W
    (fun n _ => by simp only [Set.indicator_apply]; split_ifs <;> positivity)
  calc
    _ = ∑ n ∈ W, (Nat.factoredNumbers A).indicator (fun d : ℕ => (d : ℝ)⁻¹) n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Set.indicator_of_mem (hW n hn), one_div]
    _ ≤ _ := hb

theorem removed_product_identity {Q : ℝ} {S : Finset ℕ} (hS : S ⊆ primesUpTo Q) :
    inverseProduct (primesUpTo Q \ S) = inversePrimeProduct Q * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  have hn : (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hprime := (primesUpTo_mem.mp (hS hp)).1
    have h : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)
    linarith
  have he := Finset.prod_sdiff (f := fun p : ℕ => (1 - (p : ℝ)⁻¹)⁻¹) hS
  change inverseProduct (primesUpTo Q \ S) * (∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹) =
    inversePrimeProduct Q at he
  rw [Finset.prod_inv_distrib] at he
  calc
    _ = (inverseProduct (primesUpTo Q \ S) * (∏ p ∈ S, (1 - (p : ℝ)⁻¹))⁻¹) *
        (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) := by rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]
    _ = _ := by rw [he]

theorem removed_product_bound {Q : ℝ} {S : Finset ℕ} (hS : S ⊆ primesUpTo Q) :
    inverseProduct (primesUpTo Q \ S) ≤
      inversePrimeProduct Q * Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) := by
  rw [removed_product_identity hS]
  apply mul_le_mul_of_nonneg_left _ (inversePrimeProduct_pos Q).le
  calc
    _ ≤ ∏ p ∈ S, Real.exp (-(p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hprime := (primesUpTo_mem.mp (hS hp)).1
        have h : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)
        linarith
      · intro p _
        exact Real.one_sub_le_exp_neg _
    _ = _ := by rw [← Real.exp_sum]; simp only [Finset.sum_neg_distrib, one_div]

theorem allowed_reciprocal_bound {Q : ℝ} {S W : Finset ℕ}
    (hS : S ⊆ primesUpTo Q)
    (hW : ∀ w ∈ W, w ∈ Nat.factoredNumbers (primesUpTo Q \ S)) :
    (∑ w ∈ W, (1 : ℝ) / w) ≤
      inversePrimeProduct Q * Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) :=
  (factored_partial_reciprocal_bound _ W
    (fun _ hp => (primesUpTo_mem.mp (Finset.mem_sdiff.mp hp).1).1) hW).trans
      (removed_product_bound hS)

end NField.Alignment.KorolevAllowedEulerProduct
