/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.NeutralityTheorem

/-!
# The collision invariant

Exact finite-determination, reflection-mean, and half-group arithmetic for
the Lean companion to "The Collision Invariant".
-/

namespace NField.Alignment.CollisionInvariant

open scoped BigOperators
open NField.CollisionDefinition
open NField.Alignment.BinDerangements
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower

/-! ## Bilateral parity -/

/-- A finite set preserved by a fixed-point-free involution has even
cardinality.  The proof chooses the smaller member of each two-element orbit
with an arbitrary linear order. -/
theorem even_card_of_fixedPointFree_involution
    {α : Type*} [DecidableEq α]
    (s : Finset α) (r : α → α) (key : α → ℕ)
    (hkey : Function.Injective key)
    (hinv : Function.Involutive r)
    (hstable : ∀ x, x ∈ s ↔ r x ∈ s)
    (hfree : ∀ x ∈ s, r x ≠ x) : Even s.card := by
  let lower := s.filter fun x => key x < key (r x)
  let upper := s.filter fun x => ¬key x < key (r x)
  have horbit (x : α) (hx : x ∈ s) :
      key x < key (r x) ↔ ¬key (r x) < key (r (r x)) := by
    have hne : key (r x) ≠ key x := by
      intro h
      exact hfree x hx (hkey h)
    rw [hinv x]
    omega
  have hcard : lower.card = upper.card := by
    apply Finset.card_bij (fun x _ => r x)
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxs, hxlt⟩
      apply Finset.mem_filter.mpr
      exact ⟨(hstable x).mp hxs, (horbit x hxs).mp hxlt⟩
    · intro x hx y hy hxy
      exact hinv.injective hxy
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hys, hylt⟩
      refine ⟨r y, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        have hry : r y ∈ s := (hstable y).mp hys
        exact ⟨hry, (horbit (r y) hry).mpr (by simpa [hinv y] using hylt)⟩
      · exact hinv y
  have hsplit : lower.card + upper.card = s.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := s) (fun x => key x < key (r x))
  refine ⟨lower.card, ?_⟩
  omega

private theorem complement_remainders_iff {b p x y : ℕ}
    (hx : x ≤ p) (hy : y ≤ p) :
    (p - x) % b = (p - y) % b ↔ x % b = y % b := by
  constructor
  · intro h
    have hcast : ((p - x : ℕ) : ZMod b) = (p - y : ℕ) := by
      rw [ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using h
    rw [Nat.cast_sub hx, Nat.cast_sub hy] at hcast
    have : (x : ZMod b) = (y : ZMod b) := by
      exact sub_right_inj.mp hcast
    rw [ZMod.natCast_eq_natCast_iff] at this
    simpa [Nat.ModEq] using this
  · intro h
    have hcast : (x : ZMod b) = (y : ZMod b) := by
      rw [ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using h
    have : ((p - x : ℕ) : ZMod b) = (p - y : ℕ) := by
      rw [Nat.cast_sub hx, Nat.cast_sub hy]
      exact congrArg (fun z : ZMod b => (p : ZMod b) - z) hcast
    rw [ZMod.natCast_eq_natCast_iff] at this
    simpa [Nat.ModEq] using this

/-- The finite transformed collision set whose cardinality is the collision
count after conjugation. -/
def transformedCollisionSet (b p : ℕ) [NeZero p]
    (g : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun x =>
    x ≠ 0 ∧ x.val % b = (g * x).val % b

theorem transformedCollisionCount_eq_card (b p : ℕ) [NeZero p]
    (g : ZMod p) :
    transformedCollisionCount b p g =
      (transformedCollisionSet b p g).card := by
  classical
  simp [transformedCollisionCount, transformedCollisionSet]

/-- Negation preserves the transformed collision congruence. -/
theorem mem_transformedCollisionSet_neg_iff {b p : ℕ}
    (_hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    {g x : ZMod p} (hg : g ≠ 0) :
    -x ∈ transformedCollisionSet b p g ↔
      x ∈ transformedCollisionSet b p g := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hx : x = 0
  · simp [hx, transformedCollisionSet]
  have hgx : g * x ≠ 0 := mul_ne_zero hg hx
  have hxle : x.val ≤ p := Nat.le_of_lt x.val_lt
  have hgxle : (g * x).val ≤ p := Nat.le_of_lt (g * x).val_lt
  have hnegx : (-x).val = p - x.val := by
    rw [ZMod.neg_val, if_neg hx]
  have hneggx : (g * (-x)).val = p - (g * x).val := by
    rw [show g * (-x) = -(g * x) by ring]
    rw [ZMod.neg_val, if_neg hgx]
  simp only [transformedCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [neg_ne_zero, hnegx, hneggx, complement_remainders_iff hxle hgxle]

/-- Every prime collision count is even.  This includes the identity
multiplier and does not rely on the zero-gate classification. -/
theorem transformedCollisionCount_even {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg : g ≠ 0) :
    Even (transformedCollisionCount b p g) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let s := transformedCollisionSet b p g
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hfree (x : ZMod p) (hx : x ∈ s) : -x ≠ x := by
    have hx0 : x ≠ 0 := by
      simpa [s, transformedCollisionSet] using (Finset.mem_filter.mp hx).2.1
    intro hneg
    have htwo : (2 : ZMod p) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      intro hzero
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
      exact by
        have := Nat.le_of_dvd (by omega : 0 < 2) hdvd
        omega
    have : (2 : ZMod p) * x = 0 := by
      calc
        (2 : ZMod p) * x = x + x := by ring
        _ = -x + x := by rw [hneg]
        _ = 0 := neg_add_cancel x
    exact (mul_ne_zero htwo hx0) this
  rw [transformedCollisionCount_eq_card]
  apply even_card_of_fixedPointFree_involution s (fun x => -x) ZMod.val
  · exact ZMod.val_injective p
  · intro x
    simp
  · intro x
    exact (mem_transformedCollisionSet_neg_iff (by omega) hp hg).symm
  · exact hfree

/-- Bilateral parity for the intrinsic prime digit-word collision count. -/
theorem collisionCount_even {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg : g ≠ 0) :
    Even (collisionCount (primeDigitWord b p (by omega) hp.pos) g) := by
  rw [collisionCount_eq_transformedCollisionCount (by omega) hp hbp g hg]
  exact transformedCollisionCount_even hb2 hp hbp hg

/-! ## The exact finite table and its mean -/

/-- The all-lag collision deviation is determined by the residue modulo
`b^(ell+1)` after the exact diagonal-slice reduction. -/
theorem collisionInvariant_finite_determination {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  allLagSliceDeviation_eq_table hb2 hell ha hcop

/-- Reflection of the exact finite table forces its mean over every unit
class to be exactly `-1/2`. -/
theorem collisionInvariant_grand_mean {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 := by
  apply reflection_mean_eq_negative_half
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · exact allLagUnitTable_reflection hb2 hell

/-! ## The local half-group law -/

/-- The interior wrapping predicate in least-positive unit coordinates. -/
def Wraps (m c : ℕ) [NeZero m] (a : UnitClass m) : Prop :=
  ((c : ZMod m) * a.val).val < a.val.val

instance wrapsDecidable (m c : ℕ) [NeZero m] : DecidablePred (Wraps m c) :=
  fun a => inferInstanceAs
    (Decidable (((c : ZMod m) * a.val).val < a.val.val))

/-- The manuscript's wrapping set, represented as a finite subtype. -/
abbrev WrappingClass (m c : ℕ) [NeZero m] :=
  {a : UnitClass m // Wraps m c a}

/-- Negation reverses every interior wrapping comparison. -/
theorem wraps_neg_iff {m c : ℕ} [NeZero m]
    (hc2 : 2 ≤ c) (hcm : c < m) (a : UnitClass m) :
    Wraps m c (-a) ↔ ¬ Wraps m c a := by
  letI : Fact (1 < m) := ⟨by omega⟩
  have ha0 : a.val ≠ 0 := Units.ne_zero a
  have hc0 : (c : ZMod m) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcm]
    omega
  have hca0 : (c : ZMod m) * a.val ≠ 0 := by
    intro hzero
    apply hc0
    calc
      (c : ZMod m) = (c : ZMod m) * (a.val * (a⁻¹).val) := by simp
      _ = ((c : ZMod m) * a.val) * (a⁻¹).val := by ring
      _ = 0 := by rw [hzero]; simp
  have hca_lt : ((c : ZMod m) * a.val).val < m := ZMod.val_lt _
  have ha_lt : a.val.val < m := ZMod.val_lt _
  have hca_pos : 0 < ((c : ZMod m) * a.val).val := by
    apply Nat.pos_of_ne_zero
    exact (ZMod.val_ne_zero _).mpr hca0
  have ha_pos : 0 < a.val.val := by
    apply Nat.pos_of_ne_zero
    exact (ZMod.val_ne_zero _).mpr ha0
  have hca_ne : ((c : ZMod m) * a.val).val ≠ a.val.val := by
    intro hval
    have hclass : (c : ZMod m) * a.val = a.val :=
      ZMod.val_injective m hval
    have hc_one : (c : ZMod m) = 1 := by
      calc
        (c : ZMod m) = (c : ZMod m) * (a.val * (a⁻¹).val) := by simp
        _ = ((c : ZMod m) * a.val) * (a⁻¹).val := by ring
        _ = a.val * (a⁻¹).val := by rw [hclass]
        _ = 1 := by simp
    have hcval := congrArg ZMod.val hc_one
    have : c = 1 := by
      simpa [ZMod.val_natCast_of_lt hcm, ZMod.val_one m] using hcval
    omega
  have hneg_a : (-a : UnitClass m).val.val = m - a.val.val := by
    change (-a.val).val = m - a.val.val
    rw [ZMod.neg_val, if_neg ha0]
  have hneg_ca :
      ((c : ZMod m) * (-a : UnitClass m).val).val =
        m - ((c : ZMod m) * a.val).val := by
    change ((c : ZMod m) * (-a.val)).val =
      m - ((c : ZMod m) * a.val).val
    rw [show (c : ZMod m) * (-a.val) =
        -((c : ZMod m) * a.val) by ring]
    rw [ZMod.neg_val, if_neg hca0]
  unfold Wraps
  rw [hneg_a, hneg_ca]
  constructor <;> omega

/-- Negation is an explicit equivalence from an interior wrapping set to its
complement. -/
noncomputable def wrappingComplementEquiv {m c : ℕ} [NeZero m]
    (hc2 : 2 ≤ c) (hcm : c < m) :
    WrappingClass m c ≃ {a : UnitClass m // ¬ Wraps m c a} where
  toFun a := ⟨-a.1, by
    intro hneg
    exact (wraps_neg_iff hc2 hcm a.1).mp hneg a.2⟩
  invFun a := ⟨-a.1, by
    exact (wraps_neg_iff hc2 hcm a.1).mpr a.2⟩
  left_inv a := by
    ext
    simp
  right_inv a := by
    ext
    simp

/-- Every interior wrapping set contains exactly half of the unit group. -/
theorem wrappingClass_card_eq_half {m c : ℕ} [NeZero m]
    (hc2 : 2 ≤ c) (hcm : c < m) :
    Fintype.card (WrappingClass m c) = m.totient / 2 := by
  classical
  have heq :
      Fintype.card (WrappingClass m c) =
        Fintype.card {a : UnitClass m // ¬ Wraps m c a} :=
    Fintype.card_congr (wrappingComplementEquiv hc2 hcm)
  have htotal :
      Fintype.card (UnitClass m) =
        Fintype.card (WrappingClass m c) +
          Fintype.card {a : UnitClass m // ¬ Wraps m c a} := by
    have hle : Fintype.card (WrappingClass m c) ≤
        Fintype.card (UnitClass m) := Fintype.card_subtype_le _
    rw [Fintype.card_subtype_compl]
    exact (Nat.add_sub_of_le hle).symm
  have hdouble :
      2 * Fintype.card (WrappingClass m c) = Fintype.card (UnitClass m) := by
    omega
  rw [ZMod.card_units_eq_totient] at hdouble
  omega

/-- In the manuscript's indexing `c=n+1`, every index from `1` through
`m-2` has a wrapping set of cardinality `phi(m)/2`. -/
theorem interiorWrappingClass_card {m n : ℕ} [NeZero m]
    (hm3 : 3 ≤ m) (hnlo : 1 ≤ n) (hnhi : n ≤ m - 2) :
    Fintype.card (WrappingClass m (n + 1)) = m.totient / 2 := by
  have hnadd : n + 2 ≤ m := by
    exact (Nat.le_sub_iff_add_le (by omega : 2 ≤ m)).mp hnhi
  apply wrappingClass_card_eq_half (c := n + 1)
  · omega
  · omega

end NField.Alignment.CollisionInvariant
