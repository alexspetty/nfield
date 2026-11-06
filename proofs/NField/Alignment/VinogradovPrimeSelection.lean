/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovNonsingularRecurrence
import Mathlib.Algebra.BigOperators.Associated

/-!
# Primes separating integer head tuples

The product of coordinate differences is a nonzero integer for distinct
heads. A prime family whose product exceeds its size must contain a prime
that preserves distinctness on both heads. This is the algebraic prime
selection step used before the nonsingular recurrence.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovPrimeSelection
open scoped BigOperators Classical
open VinogradovCongruencing

def separationProduct {H n : ℕ} (x y : IntervalTuple H n) : ℕ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
    ((x ij.1).val - (x ij.2).val).natAbs * ((y ij.1).val - (y ij.2).val).natAbs

theorem separationProduct_pos {H n : ℕ} (x y : IntervalTuple H n)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    0 < separationProduct x y := by
  apply Finset.prod_pos
  intro ij hij
  have hne := (Finset.mem_offDiag.mp hij).2.2
  apply Nat.mul_pos <;> apply Int.natAbs_pos.mpr <;> intro heq
  · exact hne (hx (Subtype.ext (sub_eq_zero.mp heq)))
  · exact hne (hy (Subtype.ext (sub_eq_zero.mp heq)))

theorem separationProduct_le {H n : ℕ} (hH : 1 ≤ H) (x y : IntervalTuple H n) :
    separationProduct x y ≤ H ^ (2 * n ^ 2) := by
  have hd (u : IntervalTuple H n) (i j : Fin n) :
      ((u i).val - (u j).val).natAbs ≤ H := by
    have hi := Finset.mem_Icc.mp (u i).property
    have hj := Finset.mem_Icc.mp (u j).property
    omega
  calc
    _ ≤ ∏ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag, H ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro ij _
      simpa only [pow_two] using Nat.mul_le_mul (hd x ij.1 ij.2) (hd y ij.1 ij.2)
    _ = (H ^ 2) ^ ((Finset.univ : Finset (Fin n)).offDiag.card) := by simp
    _ ≤ (H ^ 2) ^ (n ^ 2) := by
      gcongr
      · exact one_le_pow₀ hH
      · simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
          (Finset.card_le_univ (Finset.univ : Finset (Fin n)).offDiag)
    _ = _ := (pow_mul H 2 (n ^ 2)).symm

/-- Avoiding the difference product makes both reductions injective. -/
theorem nonsingular_of_not_dvd_separationProduct {p H n : ℕ}
    (x y : IntervalTuple H n) (hp : ¬ p ∣ separationProduct x y) :
    Function.Injective (fun i => ((x i).val : ZMod p)) ∧
      Function.Injective (fun i => ((y i).val : ZMod p)) := by
  have hx (i j : Fin n) (hij : i ≠ j) :
      ((x i).val - (x j).val).natAbs ∣ separationProduct x y := by
    unfold separationProduct
    exact dvd_trans (dvd_mul_right _ ((y i).val - (y j).val).natAbs)
      (Finset.dvd_prod_of_mem (fun ij : Fin n × Fin n =>
          ((x ij.1).val - (x ij.2).val).natAbs * ((y ij.1).val - (y ij.2).val).natAbs)
        (a := (i, j))
        (Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩))
  have hy (i j : Fin n) (hij : i ≠ j) :
      ((y i).val - (y j).val).natAbs ∣ separationProduct x y := by
    unfold separationProduct
    exact dvd_trans (dvd_mul_left _ ((x i).val - (x j).val).natAbs)
      (Finset.dvd_prod_of_mem (fun ij : Fin n × Fin n =>
          ((x ij.1).val - (x ij.2).val).natAbs * ((y ij.1).val - (y ij.2).val).natAbs)
        (a := (i, j))
        (Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩))
  constructor
  · intro i j heq
    by_contra hij
    apply hp
    apply dvd_trans ?_ (hx i j hij)
    apply Int.natCast_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, heq, sub_self]
  · intro i j heq
    by_contra hij
    apply hp
    apply dvd_trans ?_ (hy i j hij)
    apply Int.natCast_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, heq, sub_self]

/-- A prime family with enough product contains a separating prime for every distinct head pair. -/
theorem exists_nonsingular_prime_of_product {H n : ℕ} (hH : 1 ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : H ^ (2 * n ^ 2) < ∏ p ∈ P, p)
    (x y : IntervalTuple H n) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ p ∈ P, Function.Injective (fun i => ((x i).val : ZMod p)) ∧
      Function.Injective (fun i => ((y i).val : ZMod p)) := by
  have hex : ∃ p ∈ P, ¬ p ∣ separationProduct x y := by
    by_contra h
    push Not at h
    have hd := Finset.prod_primes_dvd (separationProduct x y)
      (fun p hp => (hP p hp).prime) h
    have hle := Nat.le_of_dvd (separationProduct_pos x y hx hy) hd
    exact (hprod.trans_le hle).not_ge (separationProduct_le hH x y)
  obtain ⟨p, hp, hsep⟩ := hex
  exact ⟨p, hp, nonsingular_of_not_dvd_separationProduct x y hsep⟩

end NField.Alignment.VinogradovPrimeSelection
