/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.Index

/-!
# Artin-Schreier fibers and the actual finite-field trace

The image of x -> x^p-x is the kernel of the trace to the prime field.
Each nonempty fiber has exactly p points.
-/

set_option autoImplicit false
namespace NField.Alignment.ArtinSchreierTrace

open scoped BigOperators

noncomputable def artinSchreier {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : K →+ K :=
  (frobenius K p).toAddMonoidHom - AddMonoidHom.id K

@[simp] theorem artinSchreier_apply {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    artinSchreier p x = x^p-x := rfl

/-- The kernel is the actual prime subfield, of cardinality p. -/
theorem artinSchreier_card_ker {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (artinSchreier (K:=K) p).ker = p := by
  let e : (artinSchreier (K:=K) p).ker ≃ (⊥ : Subfield K) :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [AddMonoidHom.mem_ker, artinSchreier_apply, sub_eq_zero]
      exact (Subfield.mem_bot_iff_pow_eq_self K p).symm)
  rw [Nat.card_congr e, Subfield.card_bot K p]

/-- Trace is invariant under Frobenius. -/
theorem trace_pow {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (x : K) :
    Algebra.trace (ZMod p) K (x^p) = Algebra.trace (ZMod p) K x := by
  have h := Algebra.trace_eq_of_algEquiv
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K) x
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using h

/-- Every Artin-Schreier value has zero trace. -/
theorem trace_artinSchreier {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (x : K) :
    Algebra.trace (ZMod p) K (x^p-x) = 0 := by
  rw [map_sub, trace_pow p, sub_self]

/-- The image equals the trace kernel, not just a subset of it. -/
theorem range_eq_trace_ker {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] :
    (artinSchreier (K:=K) p).range =
      (Algebra.trace (ZMod p) K).toAddMonoidHom.ker := by
  let f := artinSchreier (K:=K) p
  let t := (Algebra.trace (ZMod p) K).toAddMonoidHom
  have hle : f.range ≤ t.ker := by
    rintro y ⟨x, rfl⟩
    exact trace_artinSchreier p x
  have hf := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, artinSchreier_card_ker p] at hf
  have ht := t.ker.card_mul_index
  rw [AddSubgroup.index_ker] at ht
  have hsurj : Function.Surjective t := Algebra.trace_surjective (ZMod p) K
  have hr : Nat.card t.range = p := by
    rw [t.range_eq_top.mpr hsurj, Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_zmod]
  rw [hr] at ht
  have hc : Nat.card f.range = Nat.card t.ker := by
    have hp := (Fact.out : p.Prime).pos
    nlinarith
  apply SetLike.ext'
  apply Set.eq_of_subset_of_ncard_le hle
  simpa only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] using hc.ge

/-- Solvability is exactly the actual trace-zero condition. -/
theorem exists_artinSchreier_iff_trace_zero {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (v : K) :
    (∃ x : K, x^p-x = v) ↔ Algebra.trace (ZMod p) K v = 0 := by
  change v ∈ (artinSchreier (K:=K) p).range ↔ _
  rw [range_eq_trace_ker p]
  rfl

/-- Every trace-zero fiber has p points, and every other fiber is empty. -/
theorem artinSchreier_fiber_card {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (v : K) :
    (Finset.univ.filter (fun x : K => x^p-x = v)).card =
      if Algebra.trace (ZMod p) K v = 0 then p else 0 := by
  classical
  by_cases hv : Algebra.trace (ZMod p) K v = 0
  · rw [if_pos hv]
    obtain ⟨x, hx⟩ := (exists_artinSchreier_iff_trace_zero p v).mpr hv
    have heq := AddMonoidHom.card_fiber_eq_of_mem_range (artinSchreier (K:=K) p)
      (show v ∈ Set.range (artinSchreier (K:=K) p) from ⟨x, hx⟩)
      (show 0 ∈ Set.range (artinSchreier (K:=K) p) from ⟨0, map_zero _⟩)
    have hzero : (Finset.univ.filter fun g : K => artinSchreier p g = 0).card = p := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact artinSchreier_card_ker (K:=K) p
    simpa only [artinSchreier_apply] using heq.trans hzero
  · rw [if_neg hv, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    exact hv ((exists_artinSchreier_iff_trace_zero p v).mp ⟨x, (Finset.mem_filter.mp hx).2⟩)

end NField.Alignment.ArtinSchreierTrace
