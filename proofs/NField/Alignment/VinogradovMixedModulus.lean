/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovPrimePowerRigidity
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mixed-modulus Vinogradov fibers

The `j`th power sum is prescribed modulo `p^j`. Lifting every target to
`p^n` costs exactly `p^(n*(n-1)/2)` possibilities. Each nonsingular lifted
fiber has at most `n!` elements, by the checked prime-power rigidity theorem.
Mathlib supplies uniform cardinalities of homomorphism fibers, finite
products, and the fiberwise counting inequality.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.VinogradovMixedModulus

open scoped BigOperators Classical
open VinogradovDiagonal VinogradovPrimePowerRigidity

/-- Reduction between two powers of the same modulus. -/
def powerReduction (p d j : ℕ) (hj : j ≤ d) : ZMod (p ^ d) →+* ZMod (p ^ j) :=
  ZMod.castHom (pow_dvd_pow p hj) (ZMod (p ^ j))

/-- The lifts of one prescribed residue. -/
def residueLifts (p d j : ℕ) [NeZero p] (hj : j ≤ d) (b : ZMod (p ^ j)) :
    Finset (ZMod (p ^ d)) :=
  Finset.univ.filter fun a => powerReduction p d j hj a = b

/-- Every residue modulo `p^j` has exactly `p^(d-j)` lifts modulo `p^d`. -/
theorem residueLifts_card (p d j : ℕ) [NeZero p] (hj : j ≤ d)
    (b : ZMod (p ^ j)) : (residueLifts p d j hj b).card = p ^ (d - j) := by
  let f := powerReduction p d j hj
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  have heq (a : ZMod (p ^ j)) :
      (residueLifts p d j hj a).card = (residueLifts p d j hj b).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf a) (hf b)
  have hcount : p ^ d = p ^ j * (residueLifts p d j hj b).card := by
    calc
      p ^ d = (Finset.univ : Finset (ZMod (p ^ d))).card := by simp
      _ = ∑ a : ZMod (p ^ j), (residueLifts p d j hj a).card :=
        Finset.card_eq_sum_card_fiberwise (f := f) (fun _ _ => Finset.mem_univ _)
      _ = _ := by simp_rw [heq]; simp
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (NeZero.pos p) j)
  rw [← hcount, ← pow_add, Nat.add_sub_of_le hj]

/-- All simultaneous lifts of the mixed power-sum targets to modulus `p^n`. -/
def targetLifts (p n : ℕ) [NeZero p] (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    Finset (Fin n → ZMod (p ^ n)) :=
  Fintype.piFinset fun j => residueLifts p n (j.val + 1) (by omega) (b j)

/-- The exact cost of lifting the mixed targets, including the empty tuple. -/
theorem targetLifts_card (p n : ℕ) [NeZero p]
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    (targetLifts p n b).card = p ^ (n * (n - 1) / 2) := by
  have hs : (∑ j : Fin n, (n - (j.val + 1))) = n * (n - 1) / 2 := by
    calc
      _ = ∑ j : Fin n, j.val := by
        simpa [Fin.revPerm, Fin.rev, Nat.sub_sub] using
          (Equiv.sum_comp (Fin.revPerm (n := n)) (fun j : Fin n => j.val))
      _ = _ := (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n).trans
        (Finset.sum_range_id n)
  simp only [targetLifts, Fintype.card_piFinset, residueLifts_card,
    Finset.prod_pow_eq_pow_sum, hs]

/-- The first `n` power sums of an ordered `n`-tuple. -/
def powerSums {R : Type*} [CommSemiring R] {n : ℕ} (u : Fin n → R) : Fin n → R :=
  fun j => ∑ i, u i ^ (j.val + 1)

/-- A nonsingular fiber with arbitrary targets at the common modulus. -/
def liftedFiber (p n : ℕ) [NeZero p] (a : Fin n → ZMod (p ^ n)) :
    Finset (Fin n → ZMod (p ^ n)) :=
  Finset.univ.filter fun u =>
    Function.Injective (fun i => (ZMod.cast (u i) : ZMod p)) ∧ powerSums u = a

/-- Arbitrary common-modulus targets have at most `n!` nonsingular solutions. -/
theorem liftedFiber_card_le_factorial {p n : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (a : Fin n → ZMod (p ^ n)) :
    (liftedFiber p n a).card ≤ n.factorial := by
  by_cases hn : n = 0
  · subst n
    simpa using (Finset.card_le_univ (liftedFiber p 0 a))
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hne : (liftedFiber p n a).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have hu' := (Finset.mem_filter.mp hu).2
    have hsub : liftedFiber p n a ⊆ nonsingularFiber p n n hp hnpos u := by
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hv'.1, ?_⟩
      intro j
      exact congrFun (hv'.2.trans hu'.2.symm) j
    exact (Finset.card_le_card hsub).trans
      (nonsingularFiber_card_le_factorial hp hnpos hnp u hu'.1)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Nonsingular tuples satisfying the mixed-modulus power-sum equations. -/
def mixedFiber (p n : ℕ) [NeZero p]
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    Finset (Fin n → ZMod (p ^ n)) :=
  Finset.univ.filter fun u =>
    Function.Injective (fun i => (ZMod.cast (u i) : ZMod p)) ∧
      ∀ j : Fin n, powerReduction p n (j.val + 1) (by omega) (powerSums u j) = b j

/-- Linnik's mixed-modulus count at the prime-power level, with its exact constant. -/
theorem mixedFiber_card_le {p n : ℕ} [NeZero p] (hp : p.Prime) (hnp : n < p)
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    (mixedFiber p n b).card ≤ n.factorial * p ^ (n * (n - 1) / 2) := by
  have hmaps : ∀ u ∈ mixedFiber p n b, powerSums u ∈ targetLifts p n b := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).2
    exact Fintype.mem_piFinset.mpr fun j =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'.2 j⟩
  have hf : ∀ a ∈ targetLifts p n b,
      ((mixedFiber p n b).filter fun u => powerSums u = a).card ≤ n.factorial := by
    intro a _
    apply le_trans (Finset.card_le_card (t := liftedFiber p n a) ?_)
      (liftedFiber_card_le_factorial hp hnp a)
    intro u hu
    obtain ⟨hu, ha⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1, ha⟩
  simpa only [targetLifts_card] using
    Finset.card_le_mul_card_image_of_maps_to hmaps n.factorial hf

/-- The literal integer tuples with prescribed mixed power sums. -/
def integerFiber (p n : ℕ) (S : Finset ℤ)
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) : Finset (IntegerTuple S n) :=
  Finset.univ.filter fun u =>
    Function.Injective (fun i => ((u i).val : ZMod p)) ∧
      ∀ j : Fin n, (∑ i, ((u i).val : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)) = b j

/-- The mixed count applies to every integer set with injective reduction modulo `p^n`. -/
theorem integerFiber_card_le {p n : ℕ} [NeZero p] (hp : p.Prime) (hnp : n < p)
    (S : Finset ℤ) (hS : Set.InjOn (fun z : ℤ => (z : ZMod (p ^ n))) S)
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    (integerFiber p n S b).card ≤ n.factorial * p ^ (n * (n - 1) / 2) := by
  by_cases hn : n = 0
  · subst n
    simpa using (Finset.card_le_univ (integerFiber p 0 S b))
  let f : IntegerTuple S n → Fin n → ZMod (p ^ n) := fun u i => (u i).val
  have hf : Function.Injective f := by
    intro u v huv
    funext i
    exact Subtype.ext (hS (u i).property (v i).property (congrFun huv i))
  have hmaps : ∀ u ∈ integerFiber p n S b, f u ∈ mixedFiber p n b := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [f, ZMod.cast_intCast (dvd_pow_self p hn)] using hu'.1
    · intro j
      simpa only [powerSums, f, powerReduction, map_sum, map_pow, map_intCast]
        using hu'.2 j
  exact (Finset.card_le_card_of_injOn f hmaps hf.injOn).trans
    (mixedFiber_card_le hp hnp b)

/-- Reduction is injective on an integer interval of length at most the modulus. -/
theorem intCast_injOn_Ico {q H : ℕ} (a : ℤ) (hH : H ≤ q) :
    Set.InjOn (fun z : ℤ => (z : ZMod q)) (Finset.Ico a (a + H)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := Finset.mem_Ico.mp hx
  obtain ⟨hy0, hy1⟩ := Finset.mem_Ico.mp hy
  have heq : ((x - a : ℤ) : ZMod q) = ((y - a : ℤ) : ZMod q) := by
    simp only [Int.cast_sub, hxy]
  have hmod := (ZMod.intCast_eq_intCast_iff' (x - a) (y - a) q).mp heq
  have hH' : (H : ℤ) ≤ q := by exact_mod_cast hH
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hmod
  omega

/-- Linnik's exact bound on any translated integer interval, including length zero. -/
theorem mixed_interval_count_le {p n H : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n) (a : ℤ)
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    (integerFiber p n (Finset.Ico a (a + H)) b).card ≤
      n.factorial * p ^ (n * (n - 1) / 2) :=
  integerFiber_card_le hp hnp _ (intCast_injOn_Ico a hH) b

/-- The customary interval `{1,...,H}` version; the endpoint `H = p^n` is allowed. -/
theorem mixed_initial_interval_count_le {p n H : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n)
    (b : ∀ j : Fin n, ZMod (p ^ (j.val + 1))) :
    (integerFiber p n (Finset.Icc 1 (H : ℤ)) b).card ≤
      n.factorial * p ^ (n * (n - 1) / 2) := by
  have heq : Finset.Icc 1 (H : ℤ) = Finset.Ico 1 (1 + (H : ℤ)) := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [heq]
  exact mixed_interval_count_le hp hnp hH 1 b

end NField.Alignment.VinogradovMixedModulus
