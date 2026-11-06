/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovPrimeSelection

/-!
# Selecting distinct coordinates from a tuple

Tuples supported on at most `d` values admit a finite table-and-index code.
All other tuples can have `n` distinct coordinates moved to the front by a
permutation. The cardinality and permutation facts are supplied by Mathlib.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovTupleSelection
open scoped BigOperators Classical

def smallSupport {α : Type*} [Fintype α] [DecidableEq α] (l d : ℕ) : Finset (Fin l → α) :=
  Finset.univ.filter fun u => (Finset.univ.image u).card ≤ d

theorem exists_table_code {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {l d : ℕ} (u : Fin l → α) (hu : (Finset.univ.image u).card ≤ d) :
    ∃ table : Fin d → α, ∃ code : Fin l → Fin d, ∀ i, table (code i) = u i := by
  let S := Finset.univ.image u
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := {a // a ∈ S}) (β := Fin d)
    (by simpa only [Fintype.card_coe, Fintype.card_fin] using hu)
  let table := Function.extend e (fun a : {a // a ∈ S} => a.val)
    (fun _ : Fin d => Classical.choice (inferInstance : Nonempty α))
  let code (i : Fin l) := e ⟨u i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine ⟨table, code, fun i => ?_⟩
  exact e.injective.extend_apply _ _ _

/-- A repeated-value tuple is counted by its value table and its index word. -/
theorem smallSupport_card_le {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (l d : ℕ) :
    (smallSupport (α := α) l d).card ≤ Fintype.card α ^ d * d ^ l := by
  let decode : (Fin d → α) × (Fin l → Fin d) → (Fin l → α) :=
    fun tc i => tc.1 (tc.2 i)
  have hsub : smallSupport (α := α) l d ⊆ Finset.univ.image decode := by
    intro u hu
    obtain ⟨t, c, htc⟩ := exists_table_code u (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨(t, c), Finset.mem_univ _, funext htc⟩
  calc
    _ ≤ (Finset.univ.image decode).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin d → α) × (Fin l → Fin d))).card :=
      Finset.card_image_le
    _ = _ := by simp

/-- Enough distinct values can be moved into the first `n` positions. -/
theorem exists_perm_injective_head {α : Type*} [DecidableEq α] {n s : ℕ}
    (u : Fin (n + s) → α) (hu : n ≤ (Finset.univ.image u).card) :
    ∃ σ : Equiv.Perm (Fin (n + s)),
      Function.Injective (fun i : Fin n => u (σ (Fin.castAdd s i))) := by
  let S := Finset.univ.image u
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin n) (β := {a // a ∈ S})
    (by simpa only [Fintype.card_coe, Fintype.card_fin] using hu)
  have hrep (a : {a // a ∈ S}) : ∃ i, u i = a.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i, hi⟩
  let pos (a : {a // a ∈ S}) := Classical.choose (hrep a)
  have hpos (a : {a // a ∈ S}) : u (pos a) = a.val := Classical.choose_spec (hrep a)
  have hg : Function.Injective (fun i : Fin n => pos (e i)) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    rw [← hpos (e i), ← hpos (e j)]
    exact congrArg u hij
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd s)
    (fun i : Fin n => pos (e i)) (Fin.castAdd_injective n s) hg
  refine ⟨σ, fun i j hij => e.injective (Subtype.ext ?_)⟩
  simpa only [hσ, hpos] using hij

/-- Complete a choice of head indices once; noninjective choices use the identity. -/
def headPermutation {n s : ℕ} (e : Fin n → Fin (n + s)) : Equiv.Perm (Fin (n + s)) :=
  if he : Function.Injective e then
    Classical.choose (Equiv.Perm.exists_extending_pair (Fin.castAdd s) e
      (Fin.castAdd_injective n s) he)
  else Equiv.refl _

theorem headPermutation_castAdd {n s : ℕ} (e : Fin n → Fin (n + s))
    (he : Function.Injective e) (i : Fin n) : headPermutation e (Fin.castAdd s i) = e i := by
  unfold headPermutation
  rw [dif_pos he]
  exact Classical.choose_spec (Equiv.Perm.exists_extending_pair (Fin.castAdd s) e
    (Fin.castAdd_injective n s) he) i

end NField.Alignment.VinogradovTupleSelection
