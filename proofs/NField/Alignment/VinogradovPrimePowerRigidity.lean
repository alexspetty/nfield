/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovDiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Nonsingular power-sum fibers modulo prime powers

For a prime greater than the tuple length, equal power sums modulo a prime
power determine tuples with distinct reductions modulo the prime up to a
permutation. This is the algebraic input to the classical congruencing step.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovPrimePowerRigidity
open scoped BigOperators Classical
open VinogradovDiagonal

/-- Reduction from a positive prime-power modulus to the prime modulus. -/
def reduction (p d : ℕ) (hd : 0 < d) : ZMod (p ^ d) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : d ≠ 0)) (ZMod p)

theorem isUnit_of_reduction_ne_zero {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (a : ZMod (p ^ d)) (ha : reduction p d hd a ≠ 0) : IsUnit a := by
  letI : NeZero (p ^ d) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hv : ¬ p ∣ a.val := by
    intro hdiv
    apply ha
    calc
      reduction p d hd a = reduction p d hd (a.val : ZMod (p ^ d)) := by
        rw [ZMod.natCast_zmod_val]
      _ = (a.val : ZMod p) := map_natCast _ _
      _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).mpr hv

/-- A root of a split polynomial with distinct residues lifts to one of its factors. -/
theorem eq_coordinate_of_prod_sub_eq_zero {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (u : Fin n → ZMod (p ^ d))
    (hu : Function.Injective (fun i => reduction p d hd (u i)))
    (a : ZMod (p ^ d)) (ha : ∏ i, (a - u i) = 0) :
    ∃ i, a = u i := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz := congrArg (reduction p d hd) ha
  simp only [map_prod, map_sub, map_zero] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  have hi' : reduction p d hd a = reduction p d hd (u i) := sub_eq_zero.mp hi
  have hunit : IsUnit (∏ j ∈ Finset.univ.erase i, (a - u j)) := by
    apply IsUnit.prod_iff.mpr
    intro j hj
    apply isUnit_of_reduction_ne_zero hp hd
    rw [map_sub, sub_ne_zero, hi']
    intro heq
    exact (Finset.mem_erase.mp hj).1 (hu heq).symm
  have heq : (∏ j ∈ Finset.univ.erase i, (a - u j)) * (a - u i) = 0 := by
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    exact ha
  refine ⟨i, sub_eq_zero.mp ?_⟩
  exact hunit.mul_left_cancel (by simpa using heq)

/-- The nonsingular prime-power power-sum system has only permutation collisions. -/
theorem power_sum_collision_implies_perm {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hnp : n < p)
    (u v : Fin n → ZMod (p ^ d))
    (hu : Function.Injective (fun i => reduction p d hd (u i)))
    (hv : Function.Injective (fun i => reduction p d hd (v i)))
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, u i ^ j = ∑ i, v i ^ j) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, v i = u (e i) := by
  have hc : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      Function.Injective (fun z : ZMod (p ^ d) => (j : ZMod (p ^ d)) * z) := by
    intro j hj hjn
    have hunit : IsUnit (j : ZMod (p ^ d)) :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (hjn.trans_lt hnp))
    exact fun _ _ heq => hunit.mul_left_cancel heq
  have hpoly := coordinatePolynomial_eq_of_power_sums u v hc h
  have hex (i : Fin n) : ∃ j, v i = u j := by
    apply eq_coordinate_of_prod_sub_eq_zero hp hd u hu (v i)
    have heval := congrArg (Polynomial.eval (v i)) hpoly
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    rw [heval]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply hv
    change reduction p d hd (v i) = reduction p d hd (v j)
    rw [hf i, hf j, hij]
  exact ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, hf⟩

/-- The actual nonsingular fiber of the first `n` power sums. -/
def nonsingularFiber (p d n : ℕ) (hp : p.Prime) (hd : 0 < d)
    (u : Fin n → ZMod (p ^ d)) : Finset (Fin n → ZMod (p ^ d)) := by
  letI : NeZero (p ^ d) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact Finset.univ.filter fun v =>
    Function.Injective (fun i => reduction p d hd (v i)) ∧
      ∀ j : Fin n, ∑ i, v i ^ (j.val + 1) = ∑ i, u i ^ (j.val + 1)

/-- Every nonsingular prime-power fiber contains at most `n!` ordered tuples. -/
theorem nonsingularFiber_card_le_factorial {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hnp : n < p)
    (u : Fin n → ZMod (p ^ d))
    (hu : Function.Injective (fun i => reduction p d hd (u i))) :
    (nonsingularFiber p d n hp hd u).card ≤ n.factorial := by
  classical
  letI : NeZero (p ^ d) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let orbit : Finset (Fin n → ZMod (p ^ d)) :=
    Finset.univ.image (fun e : Equiv.Perm (Fin n) => fun i => u (e i))
  have hsub : nonsingularFiber p d n hp hd u ⊆ orbit := by
    intro v hv
    have hv' : Function.Injective (fun i => reduction p d hd (v i)) ∧
        ∀ j : Fin n, ∑ i, v i ^ (j.val + 1) = ∑ i, u i ^ (j.val + 1) := by
      simpa only [nonsingularFiber, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    obtain ⟨e, he⟩ := power_sum_collision_implies_perm hp hd hnp u v hu hv'.1 (by
      intro j hj hjn
      have ht := hv'.2 ⟨j - 1, by omega⟩
      simpa only [Nat.sub_add_cancel hj] using ht.symm)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, funext fun i => (he i).symm⟩
  calc
    (nonsingularFiber p d n hp hd u).card ≤ orbit.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card := Finset.card_image_le
    _ = n.factorial := by simp [Fintype.card_perm]

end NField.Alignment.VinogradovPrimePowerRigidity
