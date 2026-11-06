/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaFiberEnergy
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The exact gcd cost of merging reciprocal-sum fibers -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaFrequencyKernel
open scoped BigOperators
open KaratsubaFiberEnergy

theorem multiplication_kernel_card (m a : ℕ) [NeZero m] :
    (Finset.univ.filter fun t : ZMod m => (a : ZMod m) * t = 0).card = m.gcd a := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) a
  rw [Nat.card_eq_fintype_card] at h
  simpa [Fintype.card_subtype, AddMonoidHom.mem_ker, nsmul_eq_mul,
    Nat.card_eq_fintype_card, ZMod.card] using h

theorem fiberCount_comp_eq_sum {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (z : γ) :
    fiberCount (g ∘ f) z = ∑ y ∈ Finset.univ with g y = z, fiberCount f y := by
  classical
  symm
  simpa [fiberCount] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset α) (Finset.univ.filter fun y => g y = z) f

/-- Merging at most d populations costs at most a factor d in collision energy. -/
theorem composition_energy_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (d : ℕ)
    (hd : ∀ z, (Finset.univ.filter fun y => g y = z).card ≤ d) :
    ∑ z, fiberCount (g ∘ f) z ^ 2 ≤ d * ∑ y, fiberCount f y ^ 2 := by
  classical
  calc
    _ ≤ ∑ z, d * ∑ y ∈ Finset.univ with g y = z, fiberCount f y ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      rw [fiberCount_comp_eq_sum]
      have h := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ.filter fun y => g y = z) (fun _ => (1 : ℕ)) (fiberCount f)
      simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at h
      exact h.trans (Nat.mul_le_mul_right _ (hd z))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_fiberwise]

theorem hom_fiber_card_le_kernel {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [DecidableEq H] (g : G →+ H) (z : H) :
    (Finset.univ.filter fun y => g y = z).card ≤ Fintype.card g.ker := by
  classical
  by_cases hz : ∃ x, g x = z
  · obtain ⟨x, rfl⟩ := hz
    have h := Fintype.card_congr (g.fiberEquivKer x)
    simpa only [Fintype.card_subtype, Set.mem_preimage, Set.mem_singleton_iff] using h.le
  · have he : ∀ x, g x ≠ z := by simpa using hz
    simp [he]

theorem nsmul_energy_le {α : Type*} [Fintype α] (m a : ℕ) [NeZero m]
    (f : α → ZMod m) :
    ∑ z, fiberCount (fun x => (a : ZMod m) * f x) z ^ 2 ≤
      m.gcd a * ∑ y, fiberCount f y ^ 2 := by
  have h := composition_energy_le f (nsmulAddMonoidHom a : ZMod m →+ ZMod m)
    (Fintype.card (nsmulAddMonoidHom a : ZMod m →+ ZMod m).ker)
    (hom_fiber_card_le_kernel _)
  have hk := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) a
  simp only [Nat.card_eq_fintype_card, ZMod.card] at hk
  rw [hk] at h
  simpa [Function.comp_def, nsmul_eq_mul] using h

theorem frequency_energy_le {α : Type*} [Fintype α] {m : ℕ} [NeZero m]
    (a : ZMod m) (f : α → ZMod m) :
    ∑ z, fiberCount (fun x => a * f x) z ^ 2 ≤
      a.val.gcd m * ∑ y, fiberCount f y ^ 2 := by
  simpa only [ZMod.natCast_zmod_val, Nat.gcd_comm] using nsmul_energy_le m a.val f

open KaratsubaPrimeMoment

/-- The actual reciprocal populations pay the frequency gcd and the proved factorial cost. -/
theorem reciprocal_frequency_energy_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) (a : ZMod m) :
    (∑ z, fiberCount (fun u : PrimeTuple P k =>
      a * reciprocalSum m (fun i => (u i).val)) z ^ 2) ≤
      a.val.gcd m * (k.factorial * P.card ^ k) :=
  (frequency_energy_le a _).trans
    (Nat.mul_le_mul_left _ (reciprocal_energy_le hX hprime hcop hlower hupper hsize))

end NField.Alignment.KaratsubaFrequencyKernel
