/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovMixedModulus
import NField.Alignment.VinogradovResidueClass

/-!
# The exact restricted congruencing count

The first `n` coordinates have distinct reductions modulo `p`; the remaining
coordinates on both sides lie in one residue class. Translation gives the
mixed-modulus constraints on the first coordinates, while the actual remaining
integer equations are bounded by the shorter-interval moment count.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovCongruencing
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovMixedModulus VinogradovAffine
  VinogradovMomentFibers VinogradovResidueClass

abbrev IntervalTuple (H s : ℕ) := IntegerTuple (Finset.Icc 1 (H : ℤ)) s

/-- The possible first-coordinate tuples after the common translation. -/
def compatibleHeads (p H n : ℕ) (a : ℤ) (y : IntervalTuple H n) :
    Finset (IntervalTuple H n) :=
  Finset.univ.filter fun x =>
    Function.Injective (fun i => ((x i).val : ZMod p)) ∧
      ∀ j : Fin n,
        (∑ i, (((x i).val - a : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)) =
        ∑ i, (((y i).val - a : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)

/-- The exact mixed-modulus cost applies to the original head tuple. -/
theorem compatibleHeads_card_le {p H n : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n) (a : ℤ)
    (y : IntervalTuple H n) :
    (compatibleHeads p H n a y).card ≤ n.factorial * p ^ (n * (n - 1) / 2) := by
  let S := Finset.Ico (1 - a) (1 - a + H)
  let f : IntervalTuple H n → IntegerTuple S n := fun x i =>
    ⟨(x i).val - a, by
      have hi := Finset.mem_Icc.mp (x i).property
      apply Finset.mem_Ico.mpr
      omega⟩
  let b : ∀ j : Fin n, ZMod (p ^ (j.val + 1)) := fun j =>
    ∑ i, (((y i).val - a : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)
  have hf : Function.Injective f := by
    intro x z hxz
    funext i
    have heq := congrArg (fun t : {z // z ∈ S} => t.val) (congrFun hxz i)
    exact Subtype.ext (sub_left_inj.mp heq)
  have hmaps : ∀ x ∈ compatibleHeads p H n a y, f x ∈ integerFiber p n S b := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hx'.2⟩
    intro i j hij
    apply hx'.1
    simpa only [f, Int.cast_sub, sub_left_inj] using hij
  exact (Finset.card_le_card_of_injOn f hmaps hf.injOn).trans
    (mixed_interval_count_le hp hnp hH (1 - a) b)

/-- After subtracting the common residue, the `j`th power vanishes modulo `p^j`. -/
theorem residue_sub_pow_eq_zero {p : ℕ} [NeZero p] (r : ZMod p)
    (z : ℤ) (hz : (z : ZMod p) = r) (j : ℕ) :
    ((z - r.val : ℤ) : ZMod (p ^ j)) ^ j = 0 := by
  have hd : (p : ℤ) ∣ z - r.val := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, hz, sub_self]
  have hpow : ((p ^ j : ℕ) : ℤ) ∣ (z - r.val) ^ j := by
    exact_mod_cast pow_dvd_pow_of_dvd hd j
  rw [← Int.cast_pow]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpow

/-- Equal full power sums force the mixed congruences on the first coordinates. -/
theorem head_congruences_of_residue_equations {p n s : ℕ} [NeZero p]
    (r : ZMod p) (x y : Fin n → ℤ) (u v : Fin s → ℤ)
    (hu : ∀ i, (u i : ZMod p) = r) (hv : ∀ i, (v i : ZMod p) = r)
    (h : ∀ j : Fin n,
      (∑ i, x i ^ (j.val + 1)) + (∑ i, u i ^ (j.val + 1)) =
        (∑ i, y i ^ (j.val + 1)) + ∑ i, v i ^ (j.val + 1)) :
    ∀ j : Fin n,
      (∑ i, ((x i - r.val : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)) =
        ∑ i, ((y i - r.val : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1) := by
  have hfull : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      ∑ i, Fin.append x u i ^ j = ∑ i, Fin.append y v i ^ j := by
    intro j hj hjn
    have ht := h ⟨j - 1, by omega⟩
    simpa only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Nat.sub_add_cancel hj] using ht
  intro j
  have ht := power_sums_add (Fin.append x u) (Fin.append y v) (-(r.val : ℤ))
    hfull (j.val + 1) (by omega) (by omega)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    ← sub_eq_add_neg] at ht
  have hm := congrArg (fun z : ℤ => (z : ZMod (p ^ (j.val + 1)))) ht
  simp only [Int.cast_add, Int.cast_sum, Int.cast_pow] at hm
  have hu0 : (∑ i, ((u i - r.val : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => residue_sub_pow_eq_zero r (u i) (hu i) _
  have hv0 : (∑ i, ((v i - r.val : ℤ) : ZMod (p ^ (j.val + 1))) ^ (j.val + 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => residue_sub_pow_eq_zero r (v i) (hv i) _
  simpa only [hu0, hv0, add_zero] using hm

abbrev ResidueTuple (p H s : ℕ) (r : ZMod p) :=
  IntegerTuple (residueInterval p H r) s

/-- Remaining tuples satisfying the original integer equations with the heads fixed. -/
def tailCompletions (p H n s : ℕ) (r : ZMod p) (x y : IntervalTuple H n) :
    Finset (ResidueTuple p H s r × ResidueTuple p H s r) :=
  Finset.univ.filter fun uv =>
    momentVector n x + momentVector n uv.1 = momentVector n y + momentVector n uv.2

theorem tailCompletions_card_le {p H n s : ℕ} [NeZero p]
    (r : ZMod p) (x y : IntervalTuple H n) :
    (tailCompletions p H n s r x y).card ≤
      momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  have heq : (tailCompletions p H n s r x y).card =
      shiftedMomentCount (residueInterval p H r) s n (momentVector n x - momentVector n y) := by
    congr 1
    ext uv
    simp only [tailCompletions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      ext j
      have hj := congrFun h j
      simp only [Pi.add_apply, Pi.sub_apply] at hj ⊢
      omega
    · intro h
      ext j
      have hj := congrFun h j
      simp only [Pi.add_apply, Pi.sub_apply] at hj ⊢
      omega
  rw [heq]
  exact shifted_residue_momentCount_le r s n _

/-- An ordered pair of tuples, written as its head and tail on each side. -/
abbrev SplitPair (H n s : ℕ) :=
  (IntervalTuple H n × IntervalTuple H s) × (IntervalTuple H n × IntervalTuple H s)

/-- Solutions with a specified tail residue, retaining nonsingularity on the first side. -/
def taggedPairs (p H n s : ℕ) (r : ZMod p) : Finset (SplitPair H n s) :=
  Finset.univ.filter fun xy =>
    Function.Injective (fun i => ((xy.1.1 i).val : ZMod p)) ∧
    (∀ i, ((xy.1.2 i).val : ZMod p) = r) ∧
    (∀ i, ((xy.2.2 i).val : ZMod p) = r) ∧
    momentVector n xy.1.1 + momentVector n xy.1.2 =
      momentVector n xy.2.1 + momentVector n xy.2.2

/-- With both heads fixed, a tagged solution is an actual tail completion. -/
theorem tagged_fiber_card_le {p H n s : ℕ} [NeZero p]
    (r : ZMod p) (x y : IntervalTuple H n) :
    (((taggedPairs p H n s r).filter fun xy => xy.2.1 = y).filter
      fun xy => xy.1.1 = x).card ≤
      momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  let forget : ResidueTuple p H s r → IntervalTuple H s :=
    fun u i => ⟨(u i).val, (Finset.mem_filter.mp (u i).property).1⟩
  let f : (ResidueTuple p H s r × ResidueTuple p H s r) → SplitPair H n s :=
    fun uv => ((x, forget uv.1), (y, forget uv.2))
  apply le_trans (Finset.card_le_card_of_surjOn (s := tailCompletions p H n s r x y)
    (f := f) ?_) (tailCompletions_card_le r x y)
  intro xy hxy
  obtain ⟨hxy, hx⟩ := Finset.mem_filter.mp hxy
  obtain ⟨hxy, hy⟩ := Finset.mem_filter.mp hxy
  obtain ⟨_, hu, hv, heq⟩ := (Finset.mem_filter.mp hxy).2
  let u : ResidueTuple p H s r := fun i =>
    ⟨(xy.1.2 i).val, Finset.mem_filter.mpr ⟨(xy.1.2 i).property, hu i⟩⟩
  let v : ResidueTuple p H s r := fun i =>
    ⟨(xy.2.2 i).val, Finset.mem_filter.mpr ⟨(xy.2.2 i).property, hv i⟩⟩
  refine ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · change momentVector n x + momentVector n xy.1.2 =
      momentVector n y + momentVector n xy.2.2
    simpa only [hx, hy] using heq
  · exact Prod.ext (Prod.ext hx.symm rfl) (Prod.ext hy.symm rfl)

/-- Fixing the second head leaves only the checked mixed-modulus possibilities. -/
theorem tagged_fixed_head_card_le {p H n s : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n)
    (r : ZMod p) (y : IntervalTuple H n) :
    ((taggedPairs p H n s r).filter fun xy => xy.2.1 = y).card ≤
      n.factorial * p ^ (n * (n - 1) / 2) *
        momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  have hmaps : ∀ xy ∈ (taggedPairs p H n s r).filter (fun xy => xy.2.1 = y),
      xy.1.1 ∈ compatibleHeads p H n r.val y := by
    intro xy hxy
    obtain ⟨hxy, hy⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx, hu, hv, heq⟩ := (Finset.mem_filter.mp hxy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hx, ?_⟩
    have ht := head_congruences_of_residue_equations r
      (fun i => (xy.1.1 i).val) (fun i => (xy.2.1 i).val)
      (fun i => (xy.1.2 i).val) (fun i => (xy.2.2 i).val) hu hv
      (fun j => congrFun heq j)
    simpa only [hy] using ht
  have hcount := Finset.card_le_mul_card_image_of_maps_to hmaps
    (momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n)
    (fun x _ => tagged_fiber_card_le r x y)
  calc
    _ ≤ _ := hcount
    _ ≤ _ := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ (compatibleHeads_card_le hp hnp hH r.val y)

/-- One residue contributes the exact head cost times the shorter moment. -/
theorem taggedPairs_card_le {p H n s : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n) (r : ZMod p) :
    (taggedPairs p H n s r).card ≤
      H ^ n * (n.factorial * p ^ (n * (n - 1) / 2)) *
        momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  calc
    _ = ∑ y : IntervalTuple H n,
        ((taggedPairs p H n s r).filter fun xy => xy.2.1 = y).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _y : IntervalTuple H n,
        n.factorial * p ^ (n * (n - 1) / 2) *
          momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n :=
      Finset.sum_le_sum fun y _ => tagged_fixed_head_card_le hp hnp hH r y
    _ = _ := by simp [IntervalTuple, IntegerTuple, mul_assoc]

/-- The restricted Vinogradov pairs, with both heads nonsingular and a common tail residue. -/
def restrictedPairs (p H n s : ℕ) : Finset (SplitPair H n s) :=
  Finset.univ.filter fun xy =>
    Function.Injective (fun i => ((xy.1.1 i).val : ZMod p)) ∧
    Function.Injective (fun i => ((xy.2.1 i).val : ZMod p)) ∧
    momentVector n xy.1.1 + momentVector n xy.1.2 =
      momentVector n xy.2.1 + momentVector n xy.2.2 ∧
    ∃ r : ZMod p, (∀ i, ((xy.1.2 i).val : ZMod p) = r) ∧
      ∀ i, ((xy.2.2 i).val : ZMod p) = r

/-- The exact restricted congruencing estimate, including the factor from residue selection. -/
theorem restrictedPairs_card_le {p H n s : ℕ} [NeZero p]
    (hp : p.Prime) (hnp : n < p) (hH : H ≤ p ^ n) :
    (restrictedPairs p H n s).card ≤
      n.factorial * H ^ n * p ^ (n * (n - 1) / 2 + 1) *
        momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n := by
  have hsub : restrictedPairs p H n s ⊆
      Finset.univ.biUnion (taggedPairs p H n s) := by
    intro xy hxy
    simp only [restrictedPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    obtain ⟨hx, _, heq, r, hu, hv⟩ := hxy
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hu, hv, heq⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ r : ZMod p, (taggedPairs p H n s r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r : ZMod p, H ^ n * (n.factorial * p ^ (n * (n - 1) / 2)) *
        momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s n :=
      Finset.sum_le_sum fun r _ => taggedPairs_card_le hp hnp hH r
    _ = _ := by simp [pow_succ]; ring

end NField.Alignment.VinogradovCongruencing
