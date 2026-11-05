/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DoubleTransversality
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units

/-!
# Finite-family transversality

Normalized finite product geometry and the actual finite CRT unit group.
Mathlib supplies the finite-family CRT equivalence and finite product sums.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyTransversality
open scoped BigOperators ComplexConjugate Classical
open CollisionCharacterStructure GeneralNeutrality DoubleTransversality

def finiteMean {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ * ∑ x, f x

theorem finiteMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℂ) : finiteMean (fun x => f (e x)) = finiteMean f := by
  unfold finiteMean
  rw [Fintype.card_congr e, Equiv.sum_comp e]

theorem finiteMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℂ) :
    finiteMean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem finiteMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) :
    finiteMean (fun x : α × β => f x.1 * g x.2) = finiteMean f * finiteMean g := by
  simp only [finiteMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem finiteMean_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℂ) :
    finiteMean (fun x : ∀ i, α i => ∏ i, f i (x i)) = ∏ i, finiteMean (f i) := by
  simp only [finiteMean, Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum,
    Finset.prod_inv_distrib, Finset.prod_mul_distrib]

theorem finiteMean_pi_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (i : ι) (f : α i → ℂ) :
    finiteMean (fun x : ∀ j, α j => f (x i)) = finiteMean f := by
  let β := ∀ j : {j // j ≠ i}, α j
  have he := finiteMean_equiv (Equiv.piSplitAt i α) (fun x : α i × β => f x.1 * 1)
  calc
    _ = finiteMean (fun x : α i × β => f x.1 * 1) := by
      simpa only [Equiv.piSplitAt_apply, mul_one] using he
    _ = finiteMean f * finiteMean (fun _ : β => 1) := finiteMean_prod f (fun _ : β => 1)
    _ = _ := by rw [finiteMean_const, mul_one]

theorem coordinate_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (i : ι) (f : α i → ℂ)
    (hf : ∑ x, f x = 0) : ∑ x : ∀ j, α j, f (x i) = 0 := by
  have h := finiteMean_pi_coordinate i f
  simp only [finiteMean, hf, mul_zero] at h
  have hc : (Fintype.card (∀ i, α i) : ℂ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hc

theorem coordinate_energy {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (i : ι) (f : α i → ℂ) :
    finiteEnergy (fun x : ∀ j, α j => f (x i)) = finiteEnergy f := by
  exact (finiteEnergy_equiv (Equiv.piSplitAt i α)
    (leftLift (β := ∀ j : {j // j ≠ i}, α j) f)).trans (leftLift_energy f)

theorem coordinate_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] {i j : ι} (hij : i ≠ j)
    (f : α i → ℂ) (g : α j → ℂ) (hf : ∑ x, f x = 0) (hg : ∑ x, g x = 0) :
    finiteInner (fun x : ∀ k, α k => f (x i)) (fun x => g (x j)) = 0 := by
  classical
  let β := ∀ k : {k // k ≠ i}, α k
  let g' : β → ℂ := fun y => g (y ⟨j, Ne.symm hij⟩)
  have hg' : ∑ y : β, g' y = 0 :=
    coordinate_sum_zero (α := fun k : {k : ι // k ≠ i} => α k.val)
      ⟨j, Ne.symm hij⟩ g hg
  exact (finiteInner_equiv (Equiv.piSplitAt i α) (leftLift (β := β) f)
    (rightLift (α := α i) g')).trans
    (product_lifts_orthogonal f g' hf hg')

/-- Mathlib's finite CRT equivalence, promoted to the actual unit groups. -/
def unitPiEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : Pairwise fun i j => Nat.Coprime (m i) (m j)) :
    UnitClass (∏ i, m i) ≃* ∀ i, UnitClass (m i) :=
  (Units.mapEquiv (ZMod.prodEquivPi m hm).toMulEquiv).trans MulEquiv.piUnits

theorem unitPiEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : Pairwise fun i j => Nat.Coprime (m i) (m j))
    (u : UnitClass (∏ i, m i)) (i : ι) :
    (unitPiEquiv m hm u i).val = ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
      (ZMod (m i)) u.val := by
  exact ZMod.prodEquivPi_apply m hm u.val i

end NField.Alignment.FiniteFamilyTransversality
