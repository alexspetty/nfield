/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaPrimeReciprocalRigidity
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype

/-!
# Ordered prime tuples with equal reciprocal sums

In the short range, equality of reciprocal sums modulo the modulus fixes
the prime multiset. Each fiber therefore has at most `k!` ordered tuples.
The counting set retains repetitions and is not a set of distinct products.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.KaratsubaPrimeMoment

open scoped BigOperators
open KaratsubaPrimeReciprocalRigidity

def tupleCount {k : ℕ} (u : Fin k → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => u i = p)).card

def reciprocalSum {k : ℕ} (m : ℕ) (u : Fin k → ℕ) : ZMod m :=
  ∑ i, (u i : ZMod m)⁻¹

theorem sum_tupleCount {k : ℕ} (u : Fin k → ℕ) (S : Finset ℕ)
    (hu : ∀ i, u i ∈ S) : ∑ p ∈ S, tupleCount u p = k := by
  simpa only [tupleCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := S)
      (f := u) (fun i _ => hu i)).symm

theorem reciprocalSum_eq_count_sum {k : ℕ} (m : ℕ) (u : Fin k → ℕ)
    (S : Finset ℕ) (hu : ∀ i, u i ∈ S) :
    reciprocalSum m u = ∑ p ∈ S, (tupleCount u p : ZMod m) * (p : ZMod m)⁻¹ := by
  unfold reciprocalSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S)
    (g := u) (fun i _ => hu i)]
  apply Finset.sum_congr rfl
  intro p _hp
  calc
    (∑ i ∈ Finset.univ with u i = p, (u i : ZMod m)⁻¹) =
        ∑ _i ∈ Finset.univ with u _i = p, (p : ZMod m)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp [tupleCount, nsmul_eq_mul]

/-- Reciprocal congruences preserve every multiplicity, including repeated primes. -/
theorem tupleCount_eq_of_reciprocalSum_eq {m k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (u v : Fin k → ℕ)
    (huprime : ∀ i, (u i).Prime) (hvprime : ∀ i, (v i).Prime)
    (hucop : ∀ i, (u i).Coprime m) (hvcop : ∀ i, (v i).Coprime m)
    (hulower : ∀ i, k < u i) (hvlower : ∀ i, k < v i)
    (huupper : ∀ i, (u i : ℝ) ≤ X) (hvupper : ∀ i, (v i : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m)
    (heq : reciprocalSum m u = reciprocalSum m v) :
    ∀ p, tupleCount u p = tupleCount v p := by
  classical
  let U := Finset.univ.image u
  let V := Finset.univ.image v
  let S := U ∪ V
  have hu : ∀ i, u i ∈ S := fun i => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hv : ∀ i, v i ∈ S := fun i => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hcases : ∀ p ∈ S, (∃ i, u i = p) ∨ (∃ i, v i = p) := by
    intro p hp
    simpa only [S, U, V, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] using hp
  have hcard : S.card ≤ 2 * k := by
    have hU : U.card ≤ k := by simpa only [U, Finset.card_univ, Fintype.card_fin] using Finset.card_image_le (s := Finset.univ) (f := u)
    have hV : V.card ≤ k := by simpa only [V, Finset.card_univ, Fintype.card_fin] using Finset.card_image_le (s := Finset.univ) (f := v)
    exact (Finset.card_union_le U V).trans (by omega)
  have hp : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases hcases p hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact huprime i
    · exact hvprime i
  have hc : ∀ p ∈ S, p.Coprime m := by
    intro p hp
    rcases hcases p hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hucop i
    · exact hvcop i
  have hl : ∀ p ∈ S, k < p := by
    intro p hp
    rcases hcases p hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hulower i
    · exact hvlower i
  have hh : ∀ p ∈ S, (p : ℝ) ≤ X := by
    intro p hp
    rcases hcases p hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact huupper i
    · exact hvupper i
  have hweighted := heq
  rw [reciprocalSum_eq_count_sum m u S hu, reciprocalSum_eq_count_sum m v S hv] at hweighted
  have hr := multiplicities_eq_of_reciprocal_congruence hX hcard hp hc hl hh
    (sum_tupleCount u S hu).le (sum_tupleCount v S hv).le hsize hweighted
  intro p
  by_cases hmem : p ∈ S
  · exact hr p hmem
  · have hun : ∀ i, u i ≠ p := fun i he => hmem (he ▸ hu i)
    have hvn : ∀ i, v i ≠ p := fun i he => hmem (he ▸ hv i)
    simp [tupleCount, hun, hvn]

theorem exists_perm_of_tupleCount_eq {k : ℕ} (u v : Fin k → ℕ)
    (h : ∀ p, tupleCount u p = tupleCount v p) :
    ∃ e : Equiv.Perm (Fin k), ∀ i, v (e i) = u i := by
  classical
  let e (p : ℕ) : {i // u i = p} ≃ {i // v i = p} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype, tupleCount] using h p)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Ordered choices from the prime set; equal values at different positions are retained. -/
abbrev PrimeTuple (P : Finset ℕ) (k : ℕ) := Fin k → {p // p ∈ P}

def reciprocalFiber (P : Finset ℕ) (m k : ℕ) (u : PrimeTuple P k) : Finset (PrimeTuple P k) :=
  Finset.univ.filter fun v => reciprocalSum m (fun i => (v i).val) =
    reciprocalSum m (fun i => (u i).val)

/-- The number of ordered pairs of k-tuples with equal inverse sums modulo m. -/
def reciprocalCollisionCount (P : Finset ℕ) (m k : ℕ) : ℕ :=
  ∑ u : PrimeTuple P k, (reciprocalFiber P m k u).card

theorem reciprocalFiber_card_le {P : Finset ℕ} {m k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) (u : PrimeTuple P k) :
    (reciprocalFiber P m k u).card ≤ k.factorial := by
  classical
  let orbit : Finset (PrimeTuple P k) :=
    Finset.univ.image (fun e : Equiv.Perm (Fin k) => fun i => u (e i))
  have hsub : reciprocalFiber P m k u ⊆ orbit := by
    intro v hv
    have heq := (Finset.mem_filter.mp hv).2
    have hc := tupleCount_eq_of_reciprocalSum_eq hX (fun i => (v i).val) (fun i => (u i).val)
      (fun i => hprime _ (v i).property) (fun i => hprime _ (u i).property)
      (fun i => hcop _ (v i).property) (fun i => hcop _ (u i).property)
      (fun i => hlower _ (v i).property) (fun i => hlower _ (u i).property)
      (fun i => hupper _ (v i).property) (fun i => hupper _ (u i).property) hsize heq
    obtain ⟨e, he⟩ := exists_perm_of_tupleCount_eq _ _ hc
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_univ _, ?_⟩
    funext i
    exact Subtype.ext (he i)
  calc
    (reciprocalFiber P m k u).card ≤ orbit.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card := Finset.card_image_le
    _ = k.factorial := by simp [Fintype.card_perm]

/-- The short-range prime reciprocal moment count has the factorial bound. -/
theorem reciprocalCollisionCount_le {P : Finset ℕ} {m k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) :
    reciprocalCollisionCount P m k ≤ k.factorial * P.card ^ k := by
  calc
    reciprocalCollisionCount P m k ≤ ∑ _u : PrimeTuple P k, k.factorial :=
      Finset.sum_le_sum fun u _ => reciprocalFiber_card_le hX hprime hcop hlower hupper hsize u
    _ = _ := by simp [PrimeTuple, mul_comm]

/-- The count is the cardinality of the actual set of ordered tuple pairs. -/
theorem reciprocalCollisionCount_eq_pair_count (P : Finset ℕ) (m k : ℕ) :
    reciprocalCollisionCount P m k =
      (Finset.univ.filter (fun uv : PrimeTuple P k × PrimeTuple P k =>
        reciprocalSum m (fun i => (uv.2 i).val) =
          reciprocalSum m (fun i => (uv.1 i).val))).card := by
  classical
  simp only [reciprocalCollisionCount, reciprocalFiber, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]

end NField.Alignment.KaratsubaPrimeMoment
