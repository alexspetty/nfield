/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovIntegerHolder

/-!
# The nonsingular Vinogradov recurrence

The finite Holder inequality is applied to actual integer power-sum vectors,
then the exact restricted congruencing count reduces the free coordinates to
an interval of length `H/p+1`. Both sides retain the actual tuple counts.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovNonsingularRecurrence
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovMomentFibers VinogradovCongruencing
  VinogradovHolder VinogradovIntegerHolder

def nonsingularHeads (p H n : ℕ) : Finset (IntervalTuple H n) :=
  Finset.univ.filter fun x => Function.Injective (fun i => ((x i).val : ZMod p))

abbrev Head (p H n : ℕ) := {x // x ∈ nonsingularHeads p H n}
abbrev Coordinate (H : ℕ) := {z : ℤ // z ∈ Finset.Icc 1 (H : ℤ)}

def powerVector (n : ℕ) (z : ℤ) : Fin n → ℤ := fun j => z ^ (j.val + 1)

def nonsingularPairs (p H n s : ℕ) : Finset (SplitPair H n s) :=
  Finset.univ.filter fun xy =>
    Function.Injective (fun i => ((xy.1.1 i).val : ZMod p)) ∧
    Function.Injective (fun i => ((xy.2.1 i).val : ZMod p)) ∧
    momentVector n xy.1.1 + momentVector n xy.1.2 =
      momentVector n xy.2.1 + momentVector n xy.2.2

theorem sumMap_eq_momentVector {p H n s : ℕ} (u : Head p H n × (Fin s → Coordinate H)) :
    sumMap (fun h : Head p H n => momentVector n h.val)
      (fun z : Coordinate H => powerVector n z.val) s u =
        momentVector n u.1.val + momentVector n u.2 := by
  ext j
  simp only [sumMap, powerVector, momentVector, Pi.add_apply, Finset.sum_apply]

/-- The Fourier-domain tuple family is exactly the nonsingular integer solution set. -/
theorem collisionCount_eq_nonsingularPairs (p H n s : ℕ) :
    collisionCount (sumMap (fun h : Head p H n => momentVector n h.val)
      (fun z : Coordinate H => powerVector n z.val) s) =
        (nonsingularPairs p H n s).card := by
  unfold collisionCount
  apply Finset.card_bij (fun uv _ =>
    ((uv.1.1.val, uv.1.2), (uv.2.1.val, uv.2.2)))
  · intro uv huv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp uv.1.1.property).2,
      (Finset.mem_filter.mp uv.2.1.property).2, ?_⟩
    have h := (Finset.mem_filter.mp huv).2
    simpa only [sumMap_eq_momentVector] using h
  · intro uv _ wz _ heq
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    have ht₁ : uv.1.2 = wz.1.2 :=
      congrArg (fun z : IntervalTuple H n × IntervalTuple H s => z.2) h₁
    have ht₂ : uv.2.2 = wz.2.2 :=
      congrArg (fun z : IntervalTuple H n × IntervalTuple H s => z.2) h₂
    exact Prod.ext
      (Prod.ext (Subtype.ext (congrArg Prod.fst h₁)) ht₁)
      (Prod.ext (Subtype.ext (congrArg Prod.fst h₂)) ht₂)
  · intro xy hxy
    obtain ⟨hx, hy, heq⟩ := (Finset.mem_filter.mp hxy).2
    let x : Head p H n := ⟨xy.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    let y : Head p H n := ⟨xy.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
    refine ⟨((x, xy.1.2), (y, xy.2.2)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    simpa only [sumMap_eq_momentVector] using heq

/-- A residue-fiber Fourier count embeds into the literal tagged congruencing solutions. -/
theorem residue_collisionCount_le_tagged {p H n s : ℕ} (r : ZMod p) :
    collisionCount (sumMap (fun h : Head p H n => momentVector n h.val)
      (fun z : {z : Coordinate H // (z.val : ZMod p) = r} => powerVector n z.val.val) s) ≤
        (taggedPairs p H n s r).card := by
  let A := Head p H n × (Fin s → {z : Coordinate H // (z.val : ZMod p) = r})
  let f : A → IntervalTuple H n × IntervalTuple H s :=
    fun u => (u.1.val, fun i => (u.2 i).val)
  have hf : Function.Injective f := by
    intro u v huv
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst huv)
    · funext i
      exact Subtype.ext (congrFun (congrArg Prod.snd huv) i)
  have hmap (u : A) :
      sumMap (fun h : Head p H n => momentVector n h.val)
        (fun z : {z : Coordinate H // (z.val : ZMod p) = r} => powerVector n z.val.val) s u =
          momentVector n (f u).1 + momentVector n (f u).2 := by
    ext j
    simp only [sumMap, powerVector, momentVector, Pi.add_apply, Finset.sum_apply, f]
  unfold collisionCount
  apply Finset.card_le_card_of_injOn (fun uv : A × A => (f uv.1, f uv.2))
  · intro uv huv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp uv.1.1.property).2,
      (fun i => (uv.1.2 i).property), (fun i => (uv.2.2 i).property), ?_⟩
    have h := (Finset.mem_filter.mp huv).2
    simpa only [hmap] using h
  · intro uv _ wz _ heq
    exact Prod.ext (hf (congrArg Prod.fst heq)) (hf (congrArg Prod.snd heq))

/-- The unconditional nonsingular recurrence with every power of `p` retained. -/
theorem nonsingularPairs_card_le_shorter {p H n s : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n) (hs : 0 < s) :
    (nonsingularPairs p H n s).card ≤
      n.factorial * H ^ n * p ^ (2 * s + n * (n - 1) / 2) *
        momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  have hh := integer_partition_holder_count
    (fun h : Head p H n => momentVector n h.val)
    (fun z : Coordinate H => powerVector n z.val)
    (fun z : Coordinate H => (z.val : ZMod p)) hs
  rw [collisionCount_eq_nonsingularPairs] at hh
  simp only [ZMod.card] at hh
  calc
    _ ≤ _ := hh
    _ ≤ p ^ (2 * s - 1) * ∑ r : ZMod p, (taggedPairs p H n s r).card :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum fun r _ => residue_collisionCount_le_tagged r)
    _ ≤ p ^ (2 * s - 1) * ∑ _r : ZMod p,
        H ^ n * (n.factorial * p ^ (n * (n - 1) / 2)) *
          momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum fun r _ => taggedPairs_card_le hp hnp hH r)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id]
      have he : p ^ (2 * s) = p ^ (2 * s - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * s)]
      rw [pow_add, he]
      ring

end NField.Alignment.VinogradovNonsingularRecurrence
