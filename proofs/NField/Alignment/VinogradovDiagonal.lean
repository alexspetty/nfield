/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# The diagonal Vinogradov system

Equality of the first `n` power sums of two integer `n`-tuples determines
their multiset, including repetitions. Each diagonal fiber therefore has
at most `n!` ordered tuples. Newton's identities and polynomial root
multiplicities are supplied by Mathlib.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.VinogradovDiagonal

open scoped BigOperators Classical

/-- The coordinate multiset retains repeated values at different positions. -/
def coordinateMultiset {R : Type*} {n : ℕ} (u : Fin n → R) : Multiset R :=
  Finset.univ.val.map u

theorem coordinateMultiset_card {R : Type*} {n : ℕ} (u : Fin n → R) :
    (coordinateMultiset u).card = n := by
  simp [coordinateMultiset]

/-- Newton's identities require cancellation only by the first `n` natural scalars. -/
theorem esymm_eq_of_power_sums_of_cancel {R : Type*} [CommRing R] {n : ℕ}
    (u v : Fin n → R)
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ n → Function.Injective (fun z : R => (j : R) * z))
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j)
    (j : ℕ) (hj : j ≤ n) :
    (coordinateMultiset u).esymm j = (coordinateMultiset v).esymm j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj0 : j = 0
    · subst j
      simp [Multiset.esymm]
    have hu := congrArg (MvPolynomial.aeval u)
      (MvPolynomial.mul_esymm_eq_sum (Fin n) R j)
    have hv := congrArg (MvPolynomial.aeval v)
      (MvPolynomial.mul_esymm_eq_sum (Fin n) R j)
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
      MvPolynomial.aeval_esymm_eq_multiset_esymm] at hu hv
    have hs :
        (∑ a ∈ Finset.antidiagonal j with a.1 < j,
          (-1 : R) ^ a.1 * (coordinateMultiset u).esymm a.1 *
            MvPolynomial.aeval u (MvPolynomial.psum (Fin n) R a.2)) =
        ∑ a ∈ Finset.antidiagonal j with a.1 < j,
          (-1 : R) ^ a.1 * (coordinateMultiset v).esymm a.1 *
            MvPolynomial.aeval v (MvPolynomial.psum (Fin n) R a.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ha, halt⟩ := Finset.mem_filter.mp ha
      have hab := Finset.mem_antidiagonal.mp ha
      have he := ih a.1 halt (by omega)
      have hp := h a.2 (by omega) (by omega)
      rw [he]
      simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
      rw [hp]
    have heq : (j : R) * (coordinateMultiset u).esymm j =
        (j : R) * (coordinateMultiset v).esymm j := by
      calc
        _ = _ := hu
        _ = _ := congrArg (fun z : R => (-1 : R) ^ (j + 1) * z) hs
        _ = _ := hv.symm
    exact hc j (by omega) hj heq

/-- Equal power sums determine the monic coordinate polynomial. -/
theorem coordinatePolynomial_eq_of_power_sums {R : Type*} [CommRing R] {n : ℕ}
    (u v : Fin n → R)
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ n → Function.Injective (fun z : R => (j : R) * z))
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j) :
    (∏ i, (Polynomial.X - Polynomial.C (u i))) =
      ∏ i, (Polynomial.X - Polynomial.C (v i)) := by
  have heq :
      ((coordinateMultiset u).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((coordinateMultiset v).map fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm,
      coordinateMultiset_card, coordinateMultiset_card]
    apply Finset.sum_congr rfl
    intro j hj
    rw [esymm_eq_of_power_sums_of_cancel u v hc h j
      (by have := Finset.mem_range.mp hj; omega)]
  simpa only [coordinateMultiset, Multiset.map_map, Finset.prod, Function.comp_apply] using heq

/-- Over the integers, all positive natural scalars cancel. -/
theorem esymm_eq_of_power_sums {n : ℕ} (u v : Fin n → ℤ)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j)
    (j : ℕ) (hj : j ≤ n) :
    (coordinateMultiset u).esymm j = (coordinateMultiset v).esymm j := by
  apply esymm_eq_of_power_sums_of_cancel u v _ h j hj
  intro t ht _ x y heq
  exact mul_left_cancel₀ (by omega : (t : ℤ) ≠ 0) heq

/-- Power-sum collisions preserve the complete multiset of coordinates. -/
theorem coordinateMultiset_eq_of_power_sums {n : ℕ} (u v : Fin n → ℤ)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j) :
    coordinateMultiset u = coordinateMultiset v := by
  have heq :
      ((coordinateMultiset u).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((coordinateMultiset v).map fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm,
      coordinateMultiset_card, coordinateMultiset_card]
    apply Finset.sum_congr rfl
    intro j hj
    rw [esymm_eq_of_power_sums u v h j (by have := Finset.mem_range.mp hj; omega)]
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using
    congrArg Polynomial.roots heq

/-- Equal power sums give an actual permutation, without distinctness assumptions. -/
theorem power_sum_collision_implies_perm {n : ℕ} (u v : Fin n → ℤ)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, v i = u (e i) := by
  classical
  have hm := coordinateMultiset_eq_of_power_sums u v h
  have hc (z : ℤ) : Fintype.card {i // v i = z} = Fintype.card {i // u i = z} := by
    have hz := congrArg (Multiset.count z) hm.symm
    simpa only [coordinateMultiset, Multiset.count_map, Fintype.card_subtype,
      Finset.card_def, Finset.filter_val, eq_comm] using hz
  let ef (z : ℤ) : {i // v i = z} ≃ {i // u i = z} := Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv ef, fun i => (Equiv.ofFiberEquiv_map ef i).symm⟩

/-- Ordered tuples from a finite integer set. -/
abbrev IntegerTuple (S : Finset ℤ) (s : ℕ) := Fin s → {z // z ∈ S}

/-- All tuples with the same first `k` power sums as the given tuple. -/
def momentFiber (S : Finset ℤ) (s k : ℕ) (u : IntegerTuple S s) :
    Finset (IntegerTuple S s) :=
  Finset.univ.filter fun v => ∀ j : Fin k,
    ∑ i, (v i).val ^ (j.val + 1) = ∑ i, (u i).val ^ (j.val + 1)

/-- The number of ordered pairs solving the degree-`k` Vinogradov system. -/
def momentCount (S : Finset ℤ) (s k : ℕ) : ℕ :=
  ∑ u : IntegerTuple S s, (momentFiber S s k u).card

/-- At least as many equations as coordinates force every fiber to be diagonal. -/
theorem momentFiber_card_le_factorial (S : Finset ℤ) (s k : ℕ) (hsk : s ≤ k)
    (u : IntegerTuple S s) : (momentFiber S s k u).card ≤ s.factorial := by
  classical
  let orbit : Finset (IntegerTuple S s) :=
    Finset.univ.image (fun e : Equiv.Perm (Fin s) => fun i => u (e i))
  have hsub : momentFiber S s k u ⊆ orbit := by
    intro v hv
    have heq : ∀ j : Fin k,
        ∑ i, (v i).val ^ (j.val + 1) = ∑ i, (u i).val ^ (j.val + 1) := by
      simpa only [momentFiber, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    obtain ⟨e, he⟩ := power_sum_collision_implies_perm (fun i => (u i).val)
      (fun i => (v i).val) (by
        intro j hj hjs
        have ht := heq ⟨j - 1, by omega⟩
        simpa only [Nat.sub_add_cancel hj] using ht.symm)
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_univ _, ?_⟩
    funext i
    exact Subtype.ext (he i).symm
  calc
    (momentFiber S s k u).card ≤ orbit.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin s))).card := Finset.card_image_le
    _ = s.factorial := by simp [Fintype.card_perm]

/-- The diagonal mean-value bound retains all repetitions and ordered pairs. -/
theorem momentCount_le_factorial (S : Finset ℤ) (s k : ℕ) (hsk : s ≤ k) :
    momentCount S s k ≤ s.factorial * S.card ^ s := by
  calc
    momentCount S s k ≤ ∑ _u : IntegerTuple S s, s.factorial :=
      Finset.sum_le_sum fun u _ => momentFiber_card_le_factorial S s k hsk u
    _ = _ := by simp [IntegerTuple, mul_comm]

theorem momentCount_eq_pair_count (S : Finset ℤ) (s k : ℕ) :
    momentCount S s k =
      (Finset.univ.filter fun uv : IntegerTuple S s × IntegerTuple S s =>
        ∀ j : Fin k,
          ∑ i, (uv.2 i).val ^ (j.val + 1) =
            ∑ i, (uv.1 i).val ^ (j.val + 1)).card := by
  classical
  simp only [momentCount, momentFiber, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]

/-- The usual interval version `J_{n,n}(H) ≤ n! H^n`. -/
theorem diagonal_interval_count_le (n H : ℕ) :
    momentCount (Finset.Icc 1 (H : ℤ)) n n ≤ n.factorial * H ^ n := by
  have hc : (Finset.Icc 1 (H : ℤ)).card = H := by simp
  simpa only [hc] using momentCount_le_factorial (Finset.Icc 1 (H : ℤ)) n n le_rfl

end NField.Alignment.VinogradovDiagonal
