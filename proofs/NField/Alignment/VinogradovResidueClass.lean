/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovMomentFibers

/-!
# Shorter intervals for residue-class moment counts

An integer in `{1,...,H}` with residue `r` modulo `p` is `p*q+r.val`,
where `0 ≤ q < H/p+1`. The inclusion, affine invariance, and the checked
inhomogeneous-fiber estimate give the literal shorter-interval moment
bound. No hypothesis about a mean-value estimate is used.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovResidueClass
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovAffine VinogradovMomentFibers

/-- Enlarging the coordinate set can only increase the ordered moment count. -/
theorem momentCount_mono {S T : Finset ℤ} (hST : S ⊆ T) (s k : ℕ) :
    momentCount S s k ≤ momentCount T s k := by
  let f : IntegerTuple S s → IntegerTuple T s :=
    fun u i => ⟨(u i).val, hST (u i).property⟩
  have hf : Function.Injective f := by
    intro u v huv
    funext i
    exact Subtype.ext (congrArg (fun z : {z // z ∈ T} => z.val) (congrFun huv i))
  rw [momentCount_eq_pair_count, momentCount_eq_pair_count]
  apply Finset.card_le_card_of_injOn (fun uv => (f uv.1, f uv.2))
  · intro uv huv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp huv).2⟩
  · intro uv _ wz _ heq
    exact Prod.ext (hf (congrArg Prod.fst heq)) (hf (congrArg Prod.snd heq))

/-- One residue class inside the literal initial interval. -/
def residueInterval (p H : ℕ) (r : ZMod p) : Finset ℤ :=
  (Finset.Icc 1 (H : ℤ)).filter fun x => (x : ZMod p) = r

/-- Exact quotient reconstruction, with the zero quotient retained. -/
theorem residue_quotient_mem {p H : ℕ} [NeZero p] (r : ZMod p) {x : ℤ}
    (hx : x ∈ residueInterval p H r) :
    x / p ∈ Finset.Ico 0 ((H / p + 1 : ℕ) : ℤ) ∧
      (p : ℤ) * (x / p) + r.val = x := by
  obtain ⟨hx, hr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx0, hxH⟩ := Finset.mem_Icc.mp hx
  have hp : (0 : ℤ) < p := by exact_mod_cast NeZero.pos p
  have hq0 : 0 ≤ x / p := Int.ediv_nonneg (by omega) (le_of_lt hp)
  have hqH : x / p ≤ (H : ℤ) / p := Int.ediv_le_ediv hp hxH
  have hdiv : (H : ℤ) / p = ((H / p : ℕ) : ℤ) := by norm_cast
  have hmod : x % p = (r.val : ℤ) := by
    rw [← ZMod.val_intCast x, hr]
  constructor
  · apply Finset.mem_Ico.mpr
    rw [hdiv] at hqH
    exact ⟨hq0, by exact_mod_cast (show x / p < (H / p : ℕ) + (1 : ℤ) by omega)⟩
  · have heq := Int.emod_add_mul_ediv x (p : ℤ)
    rw [hmod] at heq
    omega

/-- Each residue interval is contained in a nonzero affine image of the shorter interval. -/
theorem residueInterval_subset_affine {p H : ℕ} [NeZero p] (r : ZMod p) :
    residueInterval p H r ⊆
      (Finset.Ico 0 ((H / p + 1 : ℕ) : ℤ)).image
        (fun q : ℤ => (p : ℤ) * q + r.val) := by
  intro x hx
  obtain ⟨hq, heq⟩ := residue_quotient_mem r hx
  exact Finset.mem_image.mpr ⟨x / p, hq, heq⟩

/-- The homogeneous residue-class count is bounded by the actual shorter-interval count. -/
theorem residue_momentCount_le {p H : ℕ} [NeZero p] (r : ZMod p) (s k : ℕ) :
    momentCount (residueInterval p H r) s k ≤
      momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s k := by
  calc
    _ ≤ _ := momentCount_mono (residueInterval_subset_affine r) s k
    _ = momentCount (Finset.Ico 0 ((H / p + 1 : ℕ) : ℤ)) s k :=
      momentCount_affine_image _ s k (p : ℤ) r.val (by exact_mod_cast NeZero.ne p)
    _ = _ := momentCount_zero_interval_eq_initial _ s k

/-- Every prescribed power-sum difference on a residue class has the same upper bound. -/
theorem shifted_residue_momentCount_le {p H : ℕ} [NeZero p]
    (r : ZMod p) (s k : ℕ) (a : Fin k → ℤ) :
    shiftedMomentCount (residueInterval p H r) s k a ≤
      momentCount (Finset.Icc 1 ((H / p + 1 : ℕ) : ℤ)) s k :=
  (shiftedMomentCount_le_momentCount _ s k a).trans (residue_momentCount_le r s k)

end NField.Alignment.VinogradovResidueClass
