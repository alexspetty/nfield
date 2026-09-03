/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTransformStrip

/-!
# The neutrality theorem

Finite quotient-carry, independent-channel, and exact two-channel algebra for
the Lean companion to "The Neutrality Theorem".
-/

namespace NField.Alignment.NeutralityTheorem

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip

/-! ## Centering and selected unions of fibers -/

/-- A surjective finite reduction map gives a globally zero centered signal. -/
theorem centeredSignal_sum_zero
    {α β K : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (hsurj : Function.Surjective ρ) :
    ∑ a, centeredSignal ρ T a = 0 := by
  classical
  rw [← Fintype.sum_fiberwise ρ (centeredSignal ρ T)]
  apply Finset.sum_eq_zero
  intro u _
  apply centeredSignal_fiber_sum_zero
  obtain ⟨a, ha⟩ := hsurj u
  exact ⟨⟨a, ha⟩⟩

/-- Any union of complete reduction fibers has centered sum zero. -/
theorem centeredSignal_selected_fibers_sum_zero
    {α β K : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (hsurj : Function.Surjective ρ)
    (selected : β → Prop) [DecidablePred selected] :
    (∑ a, (if selected (ρ a) then centeredSignal ρ T a else 0)) = 0 := by
  classical
  rw [← Fintype.sum_fiberwise ρ
    (fun a => if selected (ρ a) then centeredSignal ρ T a else 0)]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : selected u
  · have hpoint (a : Fiber ρ u) :
        (if selected (ρ a) then centeredSignal ρ T a else 0) =
          centeredSignal ρ T a := by
      simp [a.property, hu]
    simp_rw [hpoint]
    apply centeredSignal_fiber_sum_zero
    obtain ⟨a, ha⟩ := hsurj u
    exact ⟨⟨a, ha⟩⟩
  · have hpoint (a : Fiber ρ u) :
        (if selected (ρ a) then centeredSignal ρ T a else 0) = 0 := by
      simp [a.property, hu]
    simp_rw [hpoint]
    simp

/-! ## Reflection on an internal canonical slice -/

/-- A finite slice selected by a coordinate label. -/
abbrev CoordinateSlice {α γ : Type*} (label : α → γ) (j : γ) :=
  {a : α // label a = j}

/-- Reflection restricted to a slice that it preserves. -/
noncomputable def coordinateSliceReflectionEquiv
    {α γ : Type*} (label : α → γ) (j : γ)
    (rα : α → α) (hα : Function.Involutive rα)
    (hpreserve : ∀ a, label a = j → label (rα a) = j) :
    CoordinateSlice label j ≃ CoordinateSlice label j where
  toFun a := ⟨rα a, hpreserve a a.property⟩
  invFun a := ⟨rα a, hpreserve a a.property⟩
  left_inv a := Subtype.ext (hα a)
  right_inv a := Subtype.ext (hα a)

/-- On a reflection-fixed internal slice, the uncentered total has exact mean
`-1/2` whenever the slice is nonempty. -/
theorem coordinateSlice_raw_mean_eq_negative_half
    {α γ K : Type*} [Fintype α] [DecidableEq γ]
    [Field K] [CharZero K]
    (label : α → γ) (j : γ) [Nonempty (CoordinateSlice label j)]
    (T : α → K) (rα : α → α) (hα : Function.Involutive rα)
    (hpreserve : ∀ a, label a = j → label (rα a) = j)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    (Fintype.card (CoordinateSlice label j) : K)⁻¹ *
        ∑ a : CoordinateSlice label j, T a = -1 / 2 := by
  classical
  let e := coordinateSliceReflectionEquiv label j rα hα hpreserve
  have hreindex : (∑ a : CoordinateSlice label j, T (e a)) =
      ∑ a : CoordinateSlice label j, T a := by
    simpa using Equiv.sum_comp e (fun a : CoordinateSlice label j => T a)
  have htwice :
      (2 : K) * (∑ a : CoordinateSlice label j, T a) =
        -(Fintype.card (CoordinateSlice label j) : K) := by
    calc
      (2 : K) * (∑ a : CoordinateSlice label j, T a) =
          (∑ a : CoordinateSlice label j, T a) +
            ∑ a : CoordinateSlice label j, T a := by ring
      _ = (∑ a : CoordinateSlice label j, T a) +
            ∑ a : CoordinateSlice label j, T (e a) := by rw [hreindex]
      _ = ∑ a : CoordinateSlice label j, (T a + T (e a)) :=
        Finset.sum_add_distrib.symm
      _ = ∑ _a : CoordinateSlice label j, (-1 : K) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hreflect a
      _ = -(Fintype.card (CoordinateSlice label j) : K) := by simp
  have hcard : (Fintype.card (CoordinateSlice label j) : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hsum : (∑ a : CoordinateSlice label j, T a) =
      -(Fintype.card (CoordinateSlice label j) : K) / 2 := by
    linear_combination (1 / 2 : K) * htwice
  rw [hsum]
  field_simp

/-- An odd centered signal sums to zero on every internal slice preserved by
reflection. -/
theorem coordinateSlice_centered_sum_zero
    {α γ K : Type*} [Fintype α] [DecidableEq γ]
    [Field K] [CharZero K]
    (label : α → γ) (j : γ) (f : α → K)
    (rα : α → α) (hα : Function.Involutive rα)
    (hpreserve : ∀ a, label a = j → label (rα a) = j)
    (hodd : ∀ a, f (rα a) = -f a) :
    ∑ a : CoordinateSlice label j, f a = 0 := by
  classical
  let e := coordinateSliceReflectionEquiv label j rα hα hpreserve
  have hreindex : (∑ a : CoordinateSlice label j, f (e a)) =
      ∑ a : CoordinateSlice label j, f a := by
    simpa using Equiv.sum_comp e (fun a : CoordinateSlice label j => f a)
  have hneg : (∑ a : CoordinateSlice label j, f (e a)) =
      -(∑ a : CoordinateSlice label j, f a) := by
    have hpoint (a : CoordinateSlice label j) : f (e a) = -f a :=
      hodd a
    simp_rw [hpoint]
    simp only [Finset.sum_neg_distrib]
  have hself : (∑ a : CoordinateSlice label j, f a) =
      -(∑ a : CoordinateSlice label j, f a) := hreindex.symm.trans hneg
  linear_combination (1 / 2 : K) * hself

/-- Reflection gives an equivalence between two exchanged coordinate
slices. -/
noncomputable def coordinateSliceExchangeEquiv
    {α γ : Type*} (label : α → γ) (j j' : γ)
    (rα : α → α) (hα : Function.Involutive rα)
    (hforward : ∀ a, label a = j → label (rα a) = j')
    (hbackward : ∀ a, label a = j' → label (rα a) = j) :
    CoordinateSlice label j ≃ CoordinateSlice label j' where
  toFun a := ⟨rα a, hforward a a.property⟩
  invFun a := ⟨rα a, hbackward a a.property⟩
  left_inv a := Subtype.ext (hα a)
  right_inv a := Subtype.ext (hα a)

/-- Two slices exchanged by a reflection have equal cardinality, and their
raw totals add to minus that common cardinality. -/
theorem coordinateSlices_raw_pair
    {α γ K : Type*} [Fintype α] [DecidableEq γ]
    [Field K] [CharZero K]
    (label : α → γ) (j j' : γ)
    (T : α → K) (rα : α → α) (hα : Function.Involutive rα)
    (hforward : ∀ a, label a = j → label (rα a) = j')
    (hbackward : ∀ a, label a = j' → label (rα a) = j)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    Fintype.card (CoordinateSlice label j) =
        Fintype.card (CoordinateSlice label j') ∧
      (∑ a : CoordinateSlice label j, T a) +
        ∑ a : CoordinateSlice label j', T a =
          -(Fintype.card (CoordinateSlice label j) : K) := by
  classical
  let e := coordinateSliceExchangeEquiv label j j' rα hα
    hforward hbackward
  constructor
  · exact Fintype.card_congr e
  · have hreindex : (∑ a : CoordinateSlice label j, T (e a)) =
        ∑ a : CoordinateSlice label j', T a := by
      simpa using Equiv.sum_comp e
        (fun a : CoordinateSlice label j' => T a)
    rw [← hreindex, ← Finset.sum_add_distrib]
    calc
      (∑ a : CoordinateSlice label j, (T a + T (e a))) =
          ∑ _a : CoordinateSlice label j, (-1 : K) := by
        apply Finset.sum_congr rfl
        intro a _
        change T a + T (rα a) = -1
        exact hreflect a
      _ = -(Fintype.card (CoordinateSlice label j) : K) := by simp

/-- An odd centered signal has zero total across two slices exchanged by
reflection. -/
theorem coordinateSlices_centered_pair
    {α γ K : Type*} [Fintype α] [DecidableEq γ]
    [Field K] [CharZero K]
    (label : α → γ) (j j' : γ)
    (f : α → K) (rα : α → α) (hα : Function.Involutive rα)
    (hforward : ∀ a, label a = j → label (rα a) = j')
    (hbackward : ∀ a, label a = j' → label (rα a) = j)
    (hodd : ∀ a, f (rα a) = -f a) :
    (∑ a : CoordinateSlice label j, f a) +
        ∑ a : CoordinateSlice label j', f a = 0 := by
  classical
  let e := coordinateSliceExchangeEquiv label j j' rα hα
    hforward hbackward
  have hreindex : (∑ a : CoordinateSlice label j, f (e a)) =
      ∑ a : CoordinateSlice label j', f a := by
    simpa using Equiv.sum_comp e
      (fun a : CoordinateSlice label j' => f a)
  rw [← hreindex, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  change f a + f (rα a) = 0
  rw [hodd]
  ring

/-- The internal residue-three label of a canonical unit representative. -/
def internalResidueThree {m : ℕ} [NeZero m]
    (a : UnitClass m) : ZMod 3 :=
  (a.val.val : ZMod 3)

/-- Negation reflects the internal residue-three label through the table
modulus. -/
theorem internalResidueThree_neg {m : ℕ} [NeZero m]
    (hm2 : 2 ≤ m) (a : UnitClass m) :
    internalResidueThree (-a) =
      (m : ZMod 3) - internalResidueThree a := by
  letI : Fact (1 < m) := ⟨by omega⟩
  have ha0 : a.val ≠ 0 := Units.ne_zero a
  have hnegval : (-a : UnitClass m).val.val = m - a.val.val := by
    change (-a.val).val = m - a.val.val
    rw [ZMod.neg_val, if_neg ha0]
  unfold internalResidueThree
  rw [hnegval]
  exact Nat.cast_sub a.val.val_le

/-- A residue-three label satisfying `2j = m` is preserved by canonical
reflection. -/
theorem internalResidueThree_fixed_preserved
    {m : ℕ} [NeZero m] (hm2 : 2 ≤ m)
    (j : ZMod 3) (hfixed : 2 * j = (m : ZMod 3))
    (a : UnitClass m) (ha : internalResidueThree a = j) :
    internalResidueThree (-a) = j := by
  rw [internalResidueThree_neg hm2, ha, ← hfixed]
  ring

/-- Canonical reflection sends an internal residue-three slice to its
reflected label. -/
theorem internalResidueThree_reflected
    {m : ℕ} [NeZero m] (hm2 : 2 ≤ m)
    (j : ZMod 3) (a : UnitClass m)
    (ha : internalResidueThree a = j) :
    internalResidueThree (-a) = (m : ZMod 3) - j := by
  rw [internalResidueThree_neg hm2, ha]

/-! ## The quotient carry when three is coprime to the table modulus -/

/-- The unit-group Chinese remainder equivalence for a modulus coprime to
three.  Its second coordinate is the integer's true residue modulo three. -/
noncomputable def crtUnitEquiv {m : ℕ} [NeZero m]
    (h : Nat.Coprime m 3) :
    UnitClass (m * 3) ≃ UnitClass m × UnitClass 3 :=
  (((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv)

/-- One true nonzero residue-three channel after restoring the quotient
carry. -/
abbrev CarryChannel {m : ℕ} [NeZero m] (h : Nat.Coprime m 3)
    (r : UnitClass 3) :=
  {A : UnitClass (m * 3) // (crtUnitEquiv h A).2 = r}

/-- Fixing the true residue-three coordinate leaves exactly one copy of every
unit class modulo the collision-table modulus. -/
noncomputable def carryChannelEquiv {m : ℕ} [NeZero m]
    (h : Nat.Coprime m 3) (r : UnitClass 3) :
    CarryChannel h r ≃ UnitClass m where
  toFun A := (crtUnitEquiv h A).1
  invFun a := ⟨(crtUnitEquiv h).symm (a, r), by simp⟩
  left_inv A := by
    apply Subtype.ext
    apply (crtUnitEquiv h).injective
    apply Prod.ext
    · simp
    · simpa using A.property.symm
  right_inv a := by simp

/-- A lifted signal has the same sum on either true residue-three channel as
it has on the complete collision table. -/
theorem carryChannel_sum_eq {m : ℕ} [NeZero m]
    (h : Nat.Coprime m 3) (r : UnitClass 3)
    {K : Type*} [AddCommMonoid K] (f : UnitClass m → K) :
    (∑ A : CarryChannel h r, f ((crtUnitEquiv h A).1)) = ∑ a, f a := by
  simpa [carryChannelEquiv] using Equiv.sum_comp (carryChannelEquiv h r) f

/-- Each true residue-three channel is independently neutral after finite
fiber centering. -/
theorem carryChannel_centered_sum_zero
    {m : ℕ} [NeZero m] (h : Nat.Coprime m 3)
    (r : UnitClass 3) {β K : Type*}
    [Fintype β] [DecidableEq β] [Field K] [CharZero K]
    (ρ : UnitClass m → β) (T : UnitClass m → K)
    (hsurj : Function.Surjective ρ) :
    ∑ A : CarryChannel h r,
      centeredSignal ρ T ((crtUnitEquiv h A).1) = 0 := by
  rw [carryChannel_sum_eq]
  exact centeredSignal_sum_zero ρ T hsurj

/-- A finite reflection law `T(a) + T(r(a)) = -1` forces total raw mean
`-1/2`. -/
theorem reflection_mean_eq_negative_half
    {α K : Type*} [Fintype α] [Nonempty α] [Field K] [CharZero K]
    (T : α → K) (rα : α → α) (hα : Function.Involutive rα)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    (Fintype.card α : K)⁻¹ * ∑ a, T a = -1 / 2 := by
  classical
  have hreindex : (∑ a, T (rα a)) = ∑ a, T a := by
    simpa using Equiv.sum_comp hα.toPerm T
  have htwice : (2 : K) * (∑ a, T a) = -(Fintype.card α : K) := by
    calc
      (2 : K) * (∑ a, T a) = (∑ a, T a) + ∑ a, T a := by ring
      _ = (∑ a, T a) + ∑ a, T (rα a) := by rw [hreindex]
      _ = ∑ a, (T a + T (rα a)) := Finset.sum_add_distrib.symm
      _ = ∑ _a : α, (-1 : K) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hreflect a
      _ = -(Fintype.card α : K) := by simp
  have hcard : (Fintype.card α : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hsum : (∑ a, T a) = -(Fintype.card α : K) / 2 := by
    linear_combination (1 / 2 : K) * htwice
  rw [hsum]
  field_simp

/-- In the coprime carry case, the raw mean in either true residue-three
channel is the global reflection mean `-1/2`. -/
theorem carryChannel_raw_mean_eq_negative_half
    {m : ℕ} [NeZero m] (h : Nat.Coprime m 3)
    (r : UnitClass 3) {K : Type*} [Field K] [CharZero K]
    (T : UnitClass m → K) (rα : UnitClass m → UnitClass m)
    (hα : Function.Involutive rα)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    (Fintype.card (CarryChannel h r) : K)⁻¹ *
        ∑ A : CarryChannel h r, T ((crtUnitEquiv h A).1) = -1 / 2 := by
  have hcard : Fintype.card (CarryChannel h r) =
      Fintype.card (UnitClass m) :=
    Fintype.card_congr (carryChannelEquiv h r)
  rw [hcard, carryChannel_sum_eq]
  exact reflection_mean_eq_negative_half T rα hα hreflect

/-! ## The base-divisible case -/

/-- Natural reduction from units modulo `b^(ell+1)` to units modulo `b`. -/
def coarseUnitReduction (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] :
    UnitClass (allLagModulus b ell) → UnitClass b :=
  ZMod.unitsMap (show b ∣ allLagModulus b ell by
    unfold allLagModulus
    exact dvd_pow_self b (by omega))

/-- The natural coarse-unit reduction is surjective. -/
theorem coarseUnitReduction_surjective (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] :
    Function.Surjective (coarseUnitReduction b ell) := by
  exact ZMod.unitsMap_surjective (show b ∣ allLagModulus b ell by
    unfold allLagModulus
    exact dvd_pow_self b (by omega))

/-- If three divides the base, coarse reduction preserves the true
residue-three coordinate. -/
theorem coarseUnitReduction_mod_three {b ell : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (h3b : 3 ∣ b)
    (a : UnitClass (allLagModulus b ell)) :
    (coarseUnitReduction b ell a).val.val % 3 = a.val.val % 3 := by
  have hval : (coarseUnitReduction b ell a).val.val = a.val.val % b := by
    change ((a.val.cast : ZMod b).val) = a.val.val % b
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hval]
  exact Nat.mod_mod_of_dvd a.val.val h3b

/-- When three divides the base, each true residue-three channel is a union
of complete coarse reduction fibers and hence has centered sum zero. -/
theorem divisibleBase_trueChannel_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (h3b : 3 ∣ b) (r : ℕ) :
    (∑ a : UnitClass (allLagModulus b ell),
        if a.val.val % 3 = r then
          centeredSignal (coarseUnitReduction b ell)
            (allLagUnitTable b ell) a
        else 0) = 0 := by
  have hselected := centeredSignal_selected_fibers_sum_zero
    (coarseUnitReduction b ell) (allLagUnitTable b ell)
    (coarseUnitReduction_surjective b ell)
    (fun u : UnitClass b => u.val.val % 3 = r)
  simpa only [coarseUnitReduction_mod_three h3b] using hselected

/-! ## Exact finite two-channel algebra -/

/-- The nontrivial real character modulo three in integer coordinates. -/
def modThreeSign (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

theorem modThreeSign_eq_one {n : ℕ} (h : n % 3 = 1) :
    modThreeSign n = 1 := by simp [modThreeSign, h]

theorem modThreeSign_eq_neg_one {n : ℕ} (h : n % 3 = 2) :
    modThreeSign n = -1 := by simp [modThreeSign, h]

/-- The exact indicator identity behind the half-sum and half-difference
decomposition. -/
theorem modThree_channel_indicator {K : Type*} [Field K] [CharZero K]
    {n r : ℕ}
    (hn : n % 3 = 1 ∨ n % 3 = 2)
    (hr : r = 1 ∨ r = 2) :
    (if n % 3 = r then (1 : K) else 0) =
      (1 / 2 : K) *
        (1 + (modThreeSign r : K) * (modThreeSign n : K)) := by
  rcases hn with hn | hn <;> rcases hr with rfl | rfl <;>
    simp [modThreeSign, hn] <;> norm_num

/-- At every finite cutoff, either true residue-three channel is the exact
half-sum or half-difference of the total and twisted packets. -/
theorem exact_finite_channel_split
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (residue : ι → ℕ) (weight : ι → K)
    (hresidue : ∀ i, residue i % 3 = 1 ∨ residue i % 3 = 2)
    {r : ℕ} (hr : r = 1 ∨ r = 2) :
    (∑ i, if residue i % 3 = r then weight i else 0) =
      (1 / 2 : K) *
        ((∑ i, weight i) +
          (modThreeSign r : K) *
            ∑ i, (modThreeSign (residue i) : K) * weight i) := by
  classical
  calc
    (∑ i, if residue i % 3 = r then weight i else 0) =
        ∑ i, (if residue i % 3 = r then (1 : K) else 0) * weight i := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> simp_all
    _ = ∑ i, ((1 / 2 : K) *
          (1 + (modThreeSign r : K) *
            (modThreeSign (residue i) : K))) * weight i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [modThree_channel_indicator (hresidue i) hr]
    _ = ∑ i, ((1 / 2 : K) * weight i +
          ((1 / 2 : K) * (modThreeSign r : K)) *
            ((modThreeSign (residue i) : K) * weight i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (1 / 2 : K) *
        ((∑ i, weight i) +
          (modThreeSign r : K) *
            ∑ i, (modThreeSign (residue i) : K) * weight i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring

/-! ## Executable exact certificates -/

/-- The exact rational mean on a coarse natural-representative fiber. -/
def rationalFiberMean (b ell u : ℕ) : ℚ :=
  (tableFiberSum b ell u : ℚ) / (b ^ ell : ℚ)

/-- The exact rational fiber-centered finite table. -/
def rationalCenteredTable (b ell a : ℕ) : ℚ :=
  (allLagTable b ell a : ℚ) - rationalFiberMean b ell (a % b)

/-- The joint modulus used to distinguish the collision-table coordinate
from the integer's true residue modulo three. -/
def jointModulus (b ell : ℕ) : ℕ :=
  Nat.lcm (allLagModulus b ell) 3

/-- Canonical representatives in one true nonzero residue-three channel. -/
def trueChannelRepresentatives (b ell r : ℕ) : Finset ℕ :=
  (reducedResidues (jointModulus b ell)).filter fun A => A % 3 = r

/-- Exact lifted centered sum in one true residue-three channel. -/
def exactTrueChannelSum (b ell r : ℕ) : ℚ :=
  ∑ A ∈ trueChannelRepresentatives b ell r,
    rationalCenteredTable b ell (A % allLagModulus b ell)

/-- The same channel total regrouped by complete coarse fibers.  This is the
form used by the executable audit so the certificate follows the structural
proof instead of repeatedly recomputing the same fiber mean. -/
def exactCenteredFiberTotal (b ell u : ℕ) : ℚ :=
  (tableFiberSum b ell u : ℚ) -
    ((tableFiber b ell u).card : ℚ) * rationalFiberMean b ell u

/-- Every literal centered fiber total is zero. -/
theorem exactCenteredFiberTotal_eq_zero {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    exactCenteredFiberTotal b ell u = 0 := by
  have hpowNat : 0 < b ^ ell := pow_pos (by omega) _
  have hpow : (b ^ ell : ℚ) ≠ 0 := by
    exact_mod_cast hpowNat.ne'
  unfold exactCenteredFiberTotal rationalFiberMean
  rw [tableFiber_card hb2 hu]
  field_simp [hpow]
  norm_num [Nat.cast_pow]

/-- Carry-completed channel sum evaluated fiberwise.  If three is coprime to
the base, either true channel receives one complete copy of every coarse
fiber.  If three divides the base, it receives precisely the fibers with the
selected residue-three label. -/
def exactTrueChannelSumByFibers (b ell r : ℕ) : ℚ :=
  if 3 ∣ b then
    ∑ u ∈ (reducedResidues b).filter (fun u => u % 3 = r),
      exactCenteredFiberTotal b ell u
  else
    ∑ u ∈ reducedResidues b, exactCenteredFiberTotal b ell u

/-- The finite audit range stated in the manuscript. -/
def neutralityVerificationBases : Finset ℕ := Finset.Icc 2 40

/-- Every declared lag-one base has two independently zero true
residue-three channel sums. -/
theorem declared_base_range_true_channels_zero :
    ∀ b ∈ neutralityVerificationBases,
      exactTrueChannelSumByFibers b 1 1 = 0 ∧
        exactTrueChannelSumByFibers b 1 2 = 0 := by
  intro b hb
  have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hb).1
  by_cases hthree : 3 ∣ b
  · have hchannel (r : ℕ) :
        ∑ u ∈ (reducedResidues b).filter (fun u => u % 3 = r),
          exactCenteredFiberTotal b 1 u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact exactCenteredFiberTotal_eq_zero hb2 (Finset.mem_filter.mp hu).1
    constructor <;>
      simp only [exactTrueChannelSumByFibers, hthree, if_pos] <;>
      apply hchannel
  · have hall :
        ∑ u ∈ reducedResidues b, exactCenteredFiberTotal b 1 u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact exactCenteredFiberTotal_eq_zero hb2 hu
    constructor <;>
      simp only [exactTrueChannelSumByFibers, hthree] <;>
      exact hall

end NField.Alignment.NeutralityTheorem
