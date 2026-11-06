/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovTupleSelection

/-!
# From the full Vinogradov count to the nonsingular recurrence

Repeated-value tuples are counted explicitly. Permutations select distinct
heads, and a sufficiently large product of primes separates both heads.
The resulting recurrence retains the prime family, its sizes, the cost of
choosing head positions, and the shorter moment counts.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovUnrestrictedRecurrence
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovMomentFibers VinogradovCongruencing
  VinogradovNonsingularRecurrence VinogradovPrimeSelection VinogradovTupleSelection

def distinctPairs (H n s : ℕ) : Finset (SplitPair H n s) :=
  Finset.univ.filter fun xy => Function.Injective xy.1.1 ∧ Function.Injective xy.2.1 ∧
    momentVector n xy.1.1 + momentVector n xy.1.2 =
      momentVector n xy.2.1 + momentVector n xy.2.2

def splitTuple {H n s : ℕ} (σ : Equiv.Perm (Fin (n + s))) (u : IntervalTuple H (n + s)) :
    IntervalTuple H n × IntervalTuple H s :=
  (fun i => u (σ (Fin.castAdd s i)), fun i => u (σ (Fin.natAdd n i)))

def restoreTuple {H n s : ℕ} (σ : Equiv.Perm (Fin (n + s)))
    (x : IntervalTuple H n × IntervalTuple H s) : IntervalTuple H (n + s) :=
  fun i => Fin.append x.1 x.2 (σ.symm i)

theorem restore_split {H n s : ℕ} (σ : Equiv.Perm (Fin (n + s)))
    (u : IntervalTuple H (n + s)) : restoreTuple σ (splitTuple σ u) = u := by
  funext i
  change Fin.append (fun j => (u ∘ σ) (Fin.castAdd s j))
    (fun j => (u ∘ σ) (Fin.natAdd n j)) (σ.symm i) = u i
  rw [Fin.append_castAdd_natAdd]
  simp

theorem momentVector_split {H n s : ℕ} (σ : Equiv.Perm (Fin (n + s)))
    (u : IntervalTuple H (n + s)) :
    momentVector n (splitTuple σ u).1 + momentVector n (splitTuple σ u).2 =
      momentVector n u := by
  ext j
  simp only [momentVector, splitTuple, Pi.add_apply]
  rw [← Fin.sum_univ_add (fun i => (u (σ i)).val ^ (j.val + 1))]
  exact Equiv.sum_comp σ (fun i => (u i).val ^ (j.val + 1))

/-- The full count is bounded by the repeated-value error and permuted distinct heads. -/
theorem momentCount_le_distinctPairs {H n s : ℕ} (hH : 1 ≤ H) (hn : 1 ≤ n) :
    momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n ≤
      2 * H ^ (n + s + (n - 1)) * (n - 1) ^ (n + s) +
        (n + s) ^ (2 * n) * (distinctPairs H n s).card := by
  letI : Nonempty (Coordinate H) := ⟨⟨1, by simp; omega⟩⟩
  let B := smallSupport (α := Coordinate H) (n + s) (n - 1)
  let E := B ×ˢ (Finset.univ : Finset (IntervalTuple H (n + s))) ∪
    (Finset.univ : Finset (IntervalTuple H (n + s))) ×ˢ B
  let T := (Finset.univ : Finset
    ((Fin n → Fin (n + s)) × (Fin n → Fin (n + s)))) ×ˢ distinctPairs H n s
  let restore (t : ((Fin n → Fin (n + s)) × (Fin n → Fin (n + s))) ×
      SplitPair H n s) :=
    (restoreTuple (headPermutation t.1.1) t.2.1, restoreTuple (headPermutation t.1.2) t.2.2)
  let A := Finset.univ.filter fun uv : IntervalTuple H (n + s) × IntervalTuple H (n + s) =>
    momentVector n uv.1 = momentVector n uv.2
  have hcount : momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n = A.card := by
    rw [momentCount_eq_pair_count]
    congr 1
    ext uv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, momentVector]
    exact ⟨fun h j => (h j).symm, fun h j => (h j).symm⟩
  have hcover : A ⊆ E ∪ T.image restore := by
    intro uv huv
    by_cases hx : uv.1 ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩))
    by_cases hy : uv.2 ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_univ _, hy⟩))
    have hx' : n ≤ (Finset.univ.image uv.1).card := by
      simp only [B, smallSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    have hy' : n ≤ (Finset.univ.image uv.2).card := by
      simp only [B, smallSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      omega
    obtain ⟨σ, hσ⟩ := exists_perm_injective_head uv.1 hx'
    obtain ⟨τ, hτ⟩ := exists_perm_injective_head uv.2 hy'
    let eσ : Fin n → Fin (n + s) := fun i => σ (Fin.castAdd s i)
    let eτ : Fin n → Fin (n + s) := fun i => τ (Fin.castAdd s i)
    have heσ : Function.Injective eσ := σ.injective.comp (Fin.castAdd_injective n s)
    have heτ : Function.Injective eτ := τ.injective.comp (Fin.castAdd_injective n s)
    have hσ' : Function.Injective (fun i => uv.1 (headPermutation eσ (Fin.castAdd s i))) := by
      simpa only [headPermutation_castAdd eσ heσ] using hσ
    have hτ' : Function.Injective (fun i => uv.2 (headPermutation eτ (Fin.castAdd s i))) := by
      simpa only [headPermutation_castAdd eτ heτ] using hτ
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨((eσ, eτ), (splitTuple (headPermutation eσ) uv.1,
      splitTuple (headPermutation eτ) uv.2)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ', hτ', ?_⟩⟩
      rw [momentVector_split, momentVector_split]
      exact (Finset.mem_filter.mp huv).2
    · exact Prod.ext (restore_split (headPermutation eσ) uv.1)
        (restore_split (headPermutation eτ) uv.2)
  have hB : B.card ≤ H ^ (n - 1) * (n - 1) ^ (n + s) := by
    simpa only [Fintype.card_coe, Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast] using
      (smallSupport_card_le (α := Coordinate H) (n + s) (n - 1))
  have hU : (Finset.univ : Finset (IntervalTuple H (n + s))).card = H ^ (n + s) := by
    simp [IntervalTuple, IntegerTuple]
  calc
    _ = A.card := hcount
    _ ≤ (E ∪ T.image restore).card := Finset.card_le_card hcover
    _ ≤ E.card + (T.image restore).card := Finset.card_union_le _ _
    _ ≤ (B.card * H ^ (n + s) + H ^ (n + s) * B.card) + T.card := by
      apply Nat.add_le_add
      · simpa only [E, Finset.card_product, hU] using
          (Finset.card_union_le (B ×ˢ Finset.univ) (Finset.univ ×ˢ B))
      · exact Finset.card_image_le
    _ ≤ ((H ^ (n - 1) * (n - 1) ^ (n + s)) * H ^ (n + s) +
        H ^ (n + s) * (H ^ (n - 1) * (n - 1) ^ (n + s))) + T.card := by
      gcongr
    _ = _ := by
      simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fun, Fintype.card_fin, two_mul, pow_add]
      ring

/-- The prime-product argument covers every distinct-head solution. -/
theorem distinctPairs_card_le_prime_sum {H n s : ℕ} (hH : 1 ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : H ^ (2 * n ^ 2) < ∏ p ∈ P, p) :
    (distinctPairs H n s).card ≤ ∑ p ∈ P, (nonsingularPairs p H n s).card := by
  have hcover : distinctPairs H n s ⊆ P.biUnion (fun p => nonsingularPairs p H n s) := by
    intro xy hxy
    obtain ⟨hx, hy, heq⟩ := (Finset.mem_filter.mp hxy).2
    obtain ⟨p, hp, hxp, hyp⟩ := exists_nonsingular_prime_of_product hH P hP hprod
      xy.1.1 xy.2.1 hx hy
    exact Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp, hyp, heq⟩⟩
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)

/-- The complete finite recurrence, with the prime family and repeated-value error explicit. -/
theorem momentCount_le_prime_family {H n s : ℕ} (hH : 1 ≤ H) (hn : 1 ≤ n) (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hnp : ∀ p ∈ P, n < p) (hHp : ∀ p ∈ P, H ≤ p ^ n)
    (hprod : H ^ (2 * n ^ 2) < ∏ p ∈ P, p) :
    momentCount (Finset.Icc 1 (H : ℤ)) (n + s) n ≤
      2 * H ^ (n + s + (n - 1)) * (n - 1) ^ (n + s) +
        (n + s) ^ (2 * n) * ∑ p ∈ P,
          n.factorial * H ^ n * p ^ (2 * s + n * (n - 1) / 2) *
            momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  calc
    _ ≤ _ := momentCount_le_distinctPairs hH hn
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _
      (distinctPairs_card_le_prime_sum hH P hP hprod)) _
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro p hp
      letI : NeZero p := ⟨(hP p hp).ne_zero⟩
      exact nonsingularPairs_card_le_shorter (hP p hp) (hnp p hp) (hHp p hp) hs

end NField.Alignment.VinogradovUnrestrictedRecurrence
