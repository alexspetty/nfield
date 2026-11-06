/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovHolder

/-!
# Holder for actual integer power-sum systems

A sufficiently large finite modulus detects every equality in the finite
set of total integer vectors. Its cardinality cancels from the Fourier
argument, leaving the exact integer counting inequality.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovIntegerHolder
open scoped BigOperators Classical
open VinogradovHolder

/-- A finite collection of integer vectors admits a modulus detecting all its equalities. -/
theorem exists_modulus_detects_eq {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : ι,
      ((fun j => (f x j : ZMod m)) = fun j => (f y j : ZMod m)) ↔ f x = f y := by
  let B := ∑ x : ι, ∑ y : ι, ∑ j : Fin k, (f x j - f y j).natAbs
  refine ⟨B + 1, by omega, ?_⟩
  intro x y
  constructor
  · intro h
    ext j
    have hb : (f x j - f y j).natAbs ≤ B := by
      calc
        _ ≤ ∑ i : Fin k, (f x i - f y i).natAbs :=
          Finset.single_le_sum (f := fun i : Fin k => (f x i - f y i).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ ∑ v : ι, ∑ i : Fin k, (f x i - f v i).natAbs :=
          Finset.single_le_sum (f := fun v : ι => ∑ i : Fin k, (f x i - f v i).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
        _ ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum
            (f := fun u : ι => ∑ v : ι, ∑ i : Fin k, (f u i - f v i).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have hd : ((B + 1 : ℕ) : ℤ) ∣ f x j - f y j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simp only [Int.cast_sub, congrFun h j, sub_self]
    have hsmall : (f x j - f y j).natAbs < (((B + 1 : ℕ) : ℤ)).natAbs := by
      rw [Int.natAbs_natCast]
      omega
    exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hsmall)
  · intro h
    simp only [h]

/-- Coordinatewise reduction is an additive homomorphism. -/
def vectorReduction (m k : ℕ) : (Fin k → ℤ) →+ (Fin k → ZMod m) where
  toFun x := fun j => x j
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp

theorem collisionCount_eq_of_eq_iff {α G K : Type*} [Fintype α]
    [DecidableEq G] [DecidableEq K] (f : α → G) (g : α → K)
    (h : ∀ x y, f x = f y ↔ g x = g y) : collisionCount f = collisionCount g := by
  unfold collisionCount
  congr 1
  ext uv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]

/-- The finite Holder estimate transfers to literal integer vector equations. -/
theorem integer_partition_holder_count {α β ρ : Type*}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    {k s : ℕ} (f : α → Fin k → ℤ) (g : β → Fin k → ℤ)
    (c : β → ρ) (hs : 0 < s) :
    collisionCount (sumMap f g s) ≤ Fintype.card ρ ^ (2 * s - 1) *
      ∑ r : ρ, collisionCount (sumMap f (fun b : {b // c b = r} => g b.val) s) := by
  obtain ⟨m, hm, hdetect⟩ := exists_modulus_detects_eq (sumMap f g s)
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let q := vectorReduction m k
  have hall : collisionCount (sumMap (q ∘ f) (q ∘ g) s) =
      collisionCount (sumMap f g s) := by
    apply collisionCount_eq_of_eq_iff
    intro x y
    simpa [sumMap, q, vectorReduction, funext_iff] using hdetect x y
  have hclass (r : ρ) :
      collisionCount (sumMap (q ∘ f) (fun b : {b // c b = r} => q (g b.val)) s) =
        collisionCount (sumMap f (fun b : {b // c b = r} => g b.val) s) := by
    apply collisionCount_eq_of_eq_iff
    intro x y
    simpa [sumMap, q, vectorReduction, funext_iff] using
      hdetect (x.1, fun i => (x.2 i).val) (y.1, fun i => (y.2 i).val)
  have h := partition_holder_count (q ∘ f) (q ∘ g) c hs
  simpa only [hall, Function.comp_apply, hclass] using h

end NField.Alignment.VinogradovIntegerHolder
