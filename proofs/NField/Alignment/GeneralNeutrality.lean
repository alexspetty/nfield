/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.NeutralityTheorem

/-!
# The general neutrality theorem

Arbitrary-modulus quotient carry, compatible simultaneous channels, exact
channel cardinalities, and finite character identities.
-/

namespace NField.Alignment.GeneralNeutrality

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem

/-! ## Arbitrary coprime channels -/

/-- Unit-group Chinese remainder equivalence for arbitrary coprime moduli. -/
noncomputable def generalCrtUnitEquiv {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) :
    UnitClass (m * q) ≃ UnitClass m × UnitClass q :=
  (((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv)

/-- One true channel modulo an arbitrary modulus coprime to the collision
table modulus. -/
abbrev GeneralCarryChannel {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q) :=
  {A : UnitClass (m * q) // (generalCrtUnitEquiv h A).2 = r}

/-- Fixing the true residue coordinate leaves one complete copy of the unit
group modulo the collision-table modulus. -/
noncomputable def generalCarryChannelEquiv
    {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q) :
    GeneralCarryChannel h r ≃ UnitClass m where
  toFun A := (generalCrtUnitEquiv h A).1
  invFun a := ⟨(generalCrtUnitEquiv h).symm (a, r), by simp⟩
  left_inv A := by
    apply Subtype.ext
    apply (generalCrtUnitEquiv h).injective
    apply Prod.ext
    · simp
    · simpa using A.property.symm
  right_inv a := by simp

theorem generalCarryChannel_sum_eq
    {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q)
    {K : Type*} [AddCommMonoid K] (f : UnitClass m → K) :
    (∑ A : GeneralCarryChannel h r,
      f ((generalCrtUnitEquiv h A).1)) = ∑ a, f a := by
  simpa [generalCarryChannelEquiv] using
    Equiv.sum_comp (generalCarryChannelEquiv h r) f

/-- Exact size of a coprime true channel. -/
theorem generalCarryChannel_card
    {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q) :
    Fintype.card (GeneralCarryChannel h r) = m.totient := by
  rw [Fintype.card_congr (generalCarryChannelEquiv h r)]
  exact ZMod.card_units_eq_totient m

/-- Every true channel modulo a modulus coprime to the base is independently
neutral after finite fiber centering. -/
theorem generalCarryChannel_centered_sum_zero
    {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q)
    {β K : Type*} [Fintype β] [DecidableEq β]
    [Field K] [CharZero K]
    (ρ : UnitClass m → β) (T : UnitClass m → K)
    (hsurj : Function.Surjective ρ) :
    ∑ A : GeneralCarryChannel h r,
      centeredSignal ρ T ((generalCrtUnitEquiv h A).1) = 0 := by
  rw [generalCarryChannel_sum_eq]
  exact centeredSignal_sum_zero ρ T hsurj

/-- The raw mean of every coprime true channel is the global reflection mean
`-1/2`. -/
theorem generalCarryChannel_raw_mean_eq_negative_half
    {m q : ℕ} [NeZero m] [NeZero q]
    (h : Nat.Coprime m q) (r : UnitClass q)
    {K : Type*} [Field K] [CharZero K]
    (T : UnitClass m → K) (rα : UnitClass m → UnitClass m)
    (hα : Function.Involutive rα)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    (Fintype.card (GeneralCarryChannel h r) : K)⁻¹ *
        ∑ A : GeneralCarryChannel h r,
          T ((generalCrtUnitEquiv h A).1) = -1 / 2 := by
  have hcard : Fintype.card (GeneralCarryChannel h r) =
      Fintype.card (UnitClass m) :=
    Fintype.card_congr (generalCarryChannelEquiv h r)
  rw [hcard, generalCarryChannel_sum_eq]
  exact reflection_mean_eq_negative_half T rα hα hreflect

/-! ## Compatible divisor channels -/

/-- Natural reduction between unit groups along a divisibility relation. -/
def unitReduction {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m) :
    UnitClass m → UnitClass n :=
  ZMod.unitsMap h

theorem unitReduction_surjective {n m : ℕ} [NeZero n] [NeZero m]
    (h : n ∣ m) : Function.Surjective (unitReduction h) :=
  ZMod.unitsMap_surjective h

/-- Reduction through an intermediate modulus agrees with direct reduction. -/
theorem unitReduction_comp {d b m : ℕ}
    [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (a : UnitClass m) :
    unitReduction (dvd_trans hdb hbm) a =
      unitReduction hdb (unitReduction hbm a) := by
  have h := congrArg (fun F => F a) (ZMod.unitsMap_comp hdb hbm)
  exact h.symm

/-- Equality after unit reduction is the corresponding natural-number
congruence between canonical representatives. -/
theorem unitReduction_eq_iff_modEq {n m : ℕ} [NeZero n] [NeZero m]
    (h : n ∣ m) (a : UnitClass m) (b : UnitClass n) :
    unitReduction h a = b ↔ a.val.val ≡ b.val.val [MOD n] := by
  rw [Units.ext_iff, unitReduction, ZMod.unitsMap_val]
  rw [ZMod.cast_eq_val]
  conv_lhs =>
    rhs
    rw [← ZMod.natCast_zmod_val (b : ZMod n)]
  exact ZMod.natCast_eq_natCast_iff a.val.val b.val.val n

/-! ## Internal canonical residues -/

/-- The residue modulo `q` of a canonical unit representative modulo `m`. -/
def internalResidue {m q : ℕ} [NeZero m]
    (a : UnitClass m) : ZMod q :=
  (a.val.val : ZMod q)

/-- Canonical negation reflects every internal residue label through the table
modulus. -/
theorem internalResidue_neg {m q : ℕ} [NeZero m]
    (hm2 : 2 ≤ m) (a : UnitClass m) :
    internalResidue (q := q) (-a) =
      (m : ZMod q) - internalResidue (q := q) a := by
  letI : Fact (1 < m) := ⟨by omega⟩
  have ha0 : a.val ≠ 0 := Units.ne_zero a
  have hnegval : (-a : UnitClass m).val.val = m - a.val.val := by
    change (-a.val).val = m - a.val.val
    rw [ZMod.neg_val, if_neg ha0]
  unfold internalResidue
  rw [hnegval]
  exact Nat.cast_sub a.val.val_le

/-- A label satisfying `2j = m` is preserved by canonical reflection. -/
theorem internalResidue_fixed_preserved
    {m q : ℕ} [NeZero m] (hm2 : 2 ≤ m)
    (j : ZMod q) (hfixed : 2 * j = (m : ZMod q))
    (a : UnitClass m) (ha : internalResidue (q := q) a = j) :
    internalResidue (q := q) (-a) = j := by
  rw [internalResidue_neg hm2, ha, ← hfixed]
  ring

/-- Canonical reflection sends every internal slice to its reflected label. -/
theorem internalResidue_reflected
    {m q : ℕ} [NeZero m] (hm2 : 2 ≤ m)
    (j : ZMod q) (a : UnitClass m)
    (ha : internalResidue (q := q) a = j) :
    internalResidue (q := q) (-a) = (m : ZMod q) - j := by
  rw [internalResidue_neg hm2, ha]

/-- Every odd prime has one and only one internal label satisfying
`2j = m`. -/
theorem oddPrime_internal_fixed_label_existsUnique
    {m q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    ∃! j : ZMod q, 2 * j = (m : ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hzero
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hzero
    have hle : q ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    have hqle : 2 ≤ q := hq.two_le
    have heq : q = 2 := by omega
    exact hq2 heq
  refine ⟨(2 : ZMod q)⁻¹ * (m : ZMod q), ?_, ?_⟩
  · exact mul_inv_cancel_left₀ htwo _
  · intro j hj
    apply mul_left_cancel₀ htwo
    exact hj.trans (mul_inv_cancel_left₀ htwo _).symm

/-- A channel obtained by selecting complete fibers of a finite reduction. -/
abbrev SelectedFiberChannel {α β : Type*} (ρ : α → β)
    (selected : β → Prop) :=
  {a : α // selected (ρ a)}

/-- Selected complete fibers are a sigma type over their selected labels. -/
noncomputable def selectedFiberSigmaEquiv
    {α β : Type*} (ρ : α → β) (selected : β → Prop) :
    (Σ u : {u : β // selected u}, Fiber ρ u) ≃
      SelectedFiberChannel ρ selected where
  toFun z := ⟨z.2, by simpa [z.2.property] using z.1.property⟩
  invFun a := ⟨⟨ρ a, a.property⟩, ⟨a, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨⟨u, hu⟩, ⟨a, ha⟩⟩
    dsimp
    cases ha
    rfl
  right_inv a := Subtype.ext rfl

/-- Every selected union of complete centered fibers has zero sum, expressed
directly as a channel subtype. -/
theorem selectedFiberChannel_centered_sum_zero
    {α β K : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (hsurj : Function.Surjective ρ)
    (selected : β → Prop) [DecidablePred selected] :
    ∑ a : SelectedFiberChannel ρ selected, centeredSignal ρ T a = 0 := by
  classical
  let e := selectedFiberSigmaEquiv ρ selected
  calc
    (∑ a : SelectedFiberChannel ρ selected, centeredSignal ρ T a) =
        ∑ z : Σ u : {u : β // selected u}, Fiber ρ u,
          centeredSignal ρ T z.2 := by
            symm
            simpa [e, selectedFiberSigmaEquiv] using
              Equiv.sum_comp e
                (fun a : SelectedFiberChannel ρ selected => centeredSignal ρ T a)
    _ = ∑ u : {u : β // selected u},
          ∑ a : Fiber ρ u, centeredSignal ρ T a := by
            rw [Fintype.sum_sigma]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      apply centeredSignal_fiber_sum_zero
      obtain ⟨a, ha⟩ := hsurj u
      exact ⟨⟨a, ha⟩⟩

/-- The compatible channel visible inside `U_m` after simultaneous CRT
reduction to a common divisor `d`. -/
abbrev CompatibleChannel {d b m : ℕ}
    [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (r : UnitClass d) :=
  SelectedFiberChannel (unitReduction hbm)
    (fun u => unitReduction hdb u = r)

/-- Every compatible divisor channel is independently centered-neutral. -/
theorem compatibleChannel_centered_sum_zero
    {d b m : ℕ} [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (r : UnitClass d)
    (T : UnitClass m → ℂ) :
    ∑ a : CompatibleChannel hdb hbm r,
      centeredSignal (unitReduction hbm) T a = 0 :=
  selectedFiberChannel_centered_sum_zero
    (unitReduction hbm) T (unitReduction_surjective hbm)
    (fun u => unitReduction hdb u = r)

/-! ## Exact channel cardinalities -/

/-- Every finite type is the sigma type of the fibers of a function. -/
noncomputable def sigmaFiberEquiv
    {α β : Type*} (f : α → β) : (Σ y : β, Fiber f y) ≃ α where
  toFun z := z.2
  invFun a := ⟨f a, ⟨a, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨y, ⟨a, ha⟩⟩
    dsimp
    cases ha
    rfl
  right_inv a := rfl

/-- Every fiber of a surjective homomorphism of finite groups has cardinality
`|G| / |H|`. -/
theorem surjective_monoidHom_fiber_card
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq H] (f : G →* H) (hsurj : Function.Surjective f) (y : H) :
    Fintype.card (Fiber f y) = Fintype.card G / Fintype.card H := by
  classical
  have htotal : Fintype.card G =
      Fintype.card H * Fintype.card (Fiber f y) := by
    calc
      Fintype.card G = Fintype.card (Σ z : H, Fiber f z) :=
        (Fintype.card_congr (sigmaFiberEquiv f)).symm
      _ = ∑ z : H, Fintype.card (Fiber f z) := Fintype.card_sigma
      _ = ∑ _z : H, Fintype.card (Fiber f y) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Fintype.card_subtype (fun g => f g = z),
          Fintype.card_subtype (fun g => f g = y)]
        apply MonoidHom.card_fiber_eq_of_mem_range f
        · exact hsurj z
        · exact hsurj y
      _ = Fintype.card H * Fintype.card (Fiber f y) := by simp
  rw [htotal]
  rw [Nat.mul_comm (Fintype.card H)]
  exact (Nat.mul_div_left (Fintype.card (Fiber f y))
    (Fintype.card_pos_iff.mpr inferInstance)).symm

/-- A direct unit-reduction channel has the exact totient quotient size. -/
theorem unitReduction_fiber_card
    {d m : ℕ} [NeZero d] [NeZero m]
    (hdm : d ∣ m) (r : UnitClass d) :
    Fintype.card (Fiber (unitReduction hdm) r) = m.totient / d.totient := by
  unfold unitReduction
  rw [surjective_monoidHom_fiber_card (ZMod.unitsMap hdm)
    (ZMod.unitsMap_surjective hdm) r,
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]

/-- The composite compatible-channel presentation equals the direct fiber of
reduction to the divisor. -/
noncomputable def compatibleChannelEquivFiber
    {d b m : ℕ} [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (r : UnitClass d) :
    CompatibleChannel hdb hbm r ≃
      Fiber (unitReduction (dvd_trans hdb hbm)) r where
  toFun a := ⟨a, by
    rw [unitReduction_comp hdb hbm]
    exact a.property⟩
  invFun a := ⟨a, by
    change unitReduction hdb (unitReduction hbm a.val) = r
    rw [← unitReduction_comp hdb hbm]
    exact a.property⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

/-- Compatible divisor channels have cardinality `phi(m) / phi(d)`. -/
theorem compatibleChannel_card
    {d b m : ℕ} [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (r : UnitClass d) :
    Fintype.card (CompatibleChannel hdb hbm r) =
      m.totient / d.totient := by
  rw [Fintype.card_congr (compatibleChannelEquivFiber hdb hbm r)]
  exact unitReduction_fiber_card (dvd_trans hdb hbm) r

/-! ## Generalized Chinese remainder channels -/

/-- A true residue channel in the unit group modulo `lcm(m,Q)`. -/
abbrev LcmCarryChannel {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] (r : UnitClass Q) :=
  Fiber (unitReduction (Nat.dvd_lcm_right m Q)) r

/-- The compatible channel in `U_m`, determined by agreement modulo
`gcd(m,Q)`. -/
abbrev GcdCompatibleChannel {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.gcd m Q)] (r : UnitClass Q) :=
  Fiber (unitReduction (Nat.gcd_dvd_left m Q))
    (unitReduction (Nat.gcd_dvd_right m Q) r)

/-- Reduction modulo `m` sends an `lcm(m,Q)` channel into its exact
compatibility fiber. -/
def lcmCarryChannelToCompatible
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) : LcmCarryChannel (m := m) (Q := Q) r →
      GcdCompatibleChannel (m := m) (Q := Q) r :=
  fun A => ⟨unitReduction (Nat.dvd_lcm_left m Q) A.1, by
    calc
      unitReduction (Nat.gcd_dvd_left m Q)
          (unitReduction (Nat.dvd_lcm_left m Q) A.1) = unitReduction
          (dvd_trans (Nat.gcd_dvd_left m Q) (Nat.dvd_lcm_left m Q)) A.1 :=
        (unitReduction_comp _ _ A.1).symm
      _ = unitReduction
          (dvd_trans (Nat.gcd_dvd_right m Q) (Nat.dvd_lcm_right m Q)) A.1 := by
        congr 1
      _ = unitReduction (Nat.gcd_dvd_right m Q)
          (unitReduction (Nat.dvd_lcm_right m Q) A.1) :=
        unitReduction_comp _ _ A.1
      _ = unitReduction (Nat.gcd_dvd_right m Q) r := by
        exact congrArg (unitReduction (Nat.gcd_dvd_right m Q)) A.property
  ⟩

theorem lcmCarryChannelToCompatible_injective
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) : Function.Injective
      (lcmCarryChannelToCompatible (m := m) (Q := Q) r) := by
  intro A B hAB
  have hmUnit : unitReduction (Nat.dvd_lcm_left m Q) A.1 =
      unitReduction (Nat.dvd_lcm_left m Q) B.1 := by
    exact congrArg Subtype.val hAB
  have hQUnit : unitReduction (Nat.dvd_lcm_right m Q) A.1 =
      unitReduction (Nat.dvd_lcm_right m Q) B.1 :=
    A.property.trans B.property.symm
  have hm := (unitReduction_eq_iff_modEq
    (Nat.dvd_lcm_left m Q) A.1
    (unitReduction (Nat.dvd_lcm_left m Q) B.1)).1 hmUnit
  have hm' : A.1.val.val ≡ B.1.val.val [MOD m] := by
    exact hm.trans ((unitReduction_eq_iff_modEq
      (Nat.dvd_lcm_left m Q) B.1
      (unitReduction (Nat.dvd_lcm_left m Q) B.1)).1 rfl).symm
  have hQ := (unitReduction_eq_iff_modEq
    (Nat.dvd_lcm_right m Q) A.1
    (unitReduction (Nat.dvd_lcm_right m Q) B.1)).1 hQUnit
  have hQ' : A.1.val.val ≡ B.1.val.val [MOD Q] := by
    exact hQ.trans ((unitReduction_eq_iff_modEq
      (Nat.dvd_lcm_right m Q) B.1
      (unitReduction (Nat.dvd_lcm_right m Q) B.1)).1 rfl).symm
  apply Subtype.ext
  have hself := (unitReduction_eq_iff_modEq
    (dvd_refl (Nat.lcm m Q)) A.1 B.1).2 (Nat.mod_lcm hm' hQ')
  simpa [unitReduction] using hself

theorem lcmCarryChannelToCompatible_surjective
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) : Function.Surjective
      (lcmCarryChannelToCompatible (m := m) (Q := Q) r) := by
  intro a
  have hcompat := (unitReduction_eq_iff_modEq
    (Nat.gcd_dvd_left m Q) a.1
    (unitReduction (Nat.gcd_dvd_right m Q) r)).1 a.property
  have hrreduce := (unitReduction_eq_iff_modEq
    (Nat.gcd_dvd_right m Q) r
    (unitReduction (Nat.gcd_dvd_right m Q) r)).1 rfl
  have har : a.1.val.val ≡ r.val.val [MOD Nat.gcd m Q] :=
    hcompat.trans hrreduce.symm
  let z := Nat.chineseRemainder' har
  have hzlt : z.1 < Nat.lcm m Q :=
    Nat.chineseRemainder'_lt_lcm har (NeZero.ne m) (NeZero.ne Q)
  have hzm : Nat.Coprime z.1 m := by
    rw [Nat.coprime_iff_gcd_eq_one, z.property.1.gcd_eq]
    exact (ZMod.val_coe_unit_coprime a.1).gcd_eq_one
  have hzQ : Nat.Coprime z.1 Q := by
    rw [Nat.coprime_iff_gcd_eq_one, z.property.2.gcd_eq]
    exact (ZMod.val_coe_unit_coprime r).gcd_eq_one
  have hzL : Nat.Coprime z.1 (Nat.lcm m Q) := by
    apply Nat.Coprime.of_dvd_right
      (Nat.lcm_dvd (Nat.dvd_mul_right m Q) (Nat.dvd_mul_left Q m))
    exact hzm.mul_right hzQ
  let A : UnitClass (Nat.lcm m Q) := ZMod.unitOfCoprime z.1 hzL
  have hAval : A.val.val = z.1 := by
    exact ZMod.val_natCast_of_lt hzlt
  have hAq : unitReduction (Nat.dvd_lcm_right m Q) A = r := by
    apply (unitReduction_eq_iff_modEq (Nat.dvd_lcm_right m Q) A r).2
    simpa [hAval] using z.property.2
  refine ⟨⟨A, hAq⟩, ?_⟩
  apply Subtype.ext
  apply (unitReduction_eq_iff_modEq (Nat.dvd_lcm_left m Q) A a.1).2
  simpa [hAval] using z.property.1

/-- Generalized CRT identifies a true channel modulo `lcm(m,Q)` with the
compatible fiber in `U_m`. -/
noncomputable def generalizedCarryChannelEquiv
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) : LcmCarryChannel (m := m) (Q := Q) r ≃
      GcdCompatibleChannel (m := m) (Q := Q) r :=
  Equiv.ofBijective (lcmCarryChannelToCompatible (m := m) (Q := Q) r)
    ⟨lcmCarryChannelToCompatible_injective (m := m) (Q := Q) r,
      lcmCarryChannelToCompatible_surjective (m := m) (Q := Q) r⟩

/-- In the coprime case the compatible fiber is all of `U_m`. -/
noncomputable def coprimeCompatibleChannelEquiv
    {m Q : ℕ} [NeZero m] [NeZero Q] [NeZero (Nat.gcd m Q)]
    (hcop : Nat.Coprime m Q) (r : UnitClass Q) :
    GcdCompatibleChannel (m := m) (Q := Q) r ≃ UnitClass m where
  toFun a := a.1
  invFun a := ⟨a, by
    apply (unitReduction_eq_iff_modEq (Nat.gcd_dvd_left m Q) a
      (unitReduction (Nat.gcd_dvd_right m Q) r)).2
    simpa [hcop.gcd_eq_one] using
      (Nat.modEq_one : a.val.val ≡
        (unitReduction (Nat.gcd_dvd_right m Q) r).val.val [MOD 1])⟩
  left_inv a := Subtype.ext rfl
  right_inv a := rfl

/-- Sums on an `lcm(m,Q)` channel are exactly sums on its compatible
`U_m` fiber. -/
theorem lcmCarryChannel_sum_eq_compatible
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) {K : Type*} [AddCommMonoid K]
    (f : UnitClass m → K) :
    (∑ A : LcmCarryChannel (m := m) (Q := Q) r,
      f (unitReduction (Nat.dvd_lcm_left m Q) A.1)) =
        ∑ a : GcdCompatibleChannel (m := m) (Q := Q) r, f a.1 := by
  simpa [generalizedCarryChannelEquiv, lcmCarryChannelToCompatible] using
    Equiv.sum_comp (generalizedCarryChannelEquiv (m := m) (Q := Q) r)
      (fun a : GcdCompatibleChannel (m := m) (Q := Q) r => f a.1)

/-- A coprime `lcm(m,Q)` channel inherits the global reflection mean
`-1/2`. -/
theorem lcmCarryChannel_raw_mean_eq_negative_half
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (hcop : Nat.Coprime m Q) (r : UnitClass Q)
    {K : Type*} [Field K] [CharZero K]
    (T : UnitClass m → K) (rα : UnitClass m → UnitClass m)
    (hα : Function.Involutive rα)
    (hreflect : ∀ a, T a + T (rα a) = -1) :
    (Fintype.card (LcmCarryChannel (m := m) (Q := Q) r) : K)⁻¹ *
        ∑ A : LcmCarryChannel (m := m) (Q := Q) r,
          T (unitReduction (Nat.dvd_lcm_left m Q) A.1) = -1 / 2 := by
  have hcard : Fintype.card (LcmCarryChannel (m := m) (Q := Q) r) =
      Fintype.card (UnitClass m) :=
    (Fintype.card_congr
      (generalizedCarryChannelEquiv (m := m) (Q := Q) r)).trans
      (Fintype.card_congr
        (coprimeCompatibleChannelEquiv (m := m) (Q := Q) hcop r))
  have hsum :
      (∑ a : GcdCompatibleChannel (m := m) (Q := Q) r, T a.1) =
        ∑ a : UnitClass m, T a := by
    simpa [coprimeCompatibleChannelEquiv] using
      Equiv.sum_comp
        (coprimeCompatibleChannelEquiv (m := m) (Q := Q) hcop r) T
  rw [hcard, lcmCarryChannel_sum_eq_compatible, hsum]
  exact reflection_mean_eq_negative_half T rα hα hreflect

/-- A direct compatible fiber has zero centered sum. -/
theorem directCompatibleChannel_centered_sum_zero
    {d b m : ℕ} [NeZero d] [NeZero b] [NeZero m]
    (hdb : d ∣ b) (hbm : b ∣ m) (r : UnitClass d)
    (T : UnitClass m → ℂ) :
    (∑ a : Fiber (unitReduction (dvd_trans hdb hbm)) r,
      centeredSignal (unitReduction hbm) T a.1) = 0 := by
  let e := compatibleChannelEquivFiber hdb hbm r
  have hreindex := Equiv.sum_comp e
    (fun a : Fiber (unitReduction (dvd_trans hdb hbm)) r =>
      centeredSignal (unitReduction hbm) T a.1)
  rw [← hreindex]
  exact compatibleChannel_centered_sum_zero hdb hbm r T

/-- A squarefree modulus has the same gcd with a positive power of the base
as it has with the base. -/
theorem squarefree_gcd_pow_right {Q b k : ℕ}
    (hQ : Squarefree Q) (hk : k ≠ 0) :
    Nat.gcd Q (b ^ k) = Nat.gcd Q b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left Q (b ^ k))
    have hs : Squarefree (Nat.gcd Q (b ^ k)) :=
      hQ.squarefree_of_dvd (Nat.gcd_dvd_left Q (b ^ k))
    exact (hs.dvd_pow_iff_dvd hk).1 (Nat.gcd_dvd_right Q (b ^ k))
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left Q b)
    exact (Nat.gcd_dvd_right Q b).trans (dvd_pow_self b hk)

/-- For a squarefree channel modulus, compatibility with the complete table
is compatibility with the base. -/
theorem squarefree_table_gcd {Q b ell : ℕ} (hQ : Squarefree Q) :
    Nat.gcd (allLagModulus b ell) Q = Nat.gcd b Q := by
  rw [Nat.gcd_comm (allLagModulus b ell) Q,
    Nat.gcd_comm b Q]
  exact squarefree_gcd_pow_right hQ (by omega)

/-- Every squarefree simultaneous residue channel is centered-neutral. -/
theorem simultaneous_squarefree_channel_neutral
    {b ell Q : ℕ} [NeZero b] [NeZero Q]
    [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hQ : Squarefree Q) (r : UnitClass Q) :
    (∑ A : LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r,
      centeredSignal (coarseUnitReduction b ell) (allLagUnitTable b ell)
        (unitReduction (Nat.dvd_lcm_left (allLagModulus b ell) Q) A.1)) = 0 := by
  let m := allLagModulus b ell
  let d := Nat.gcd m Q
  have hd_eq : d = Nat.gcd b Q := by
    exact squarefree_table_gcd hQ
  have hdb : d ∣ b := by
    rw [hd_eq]
    exact Nat.gcd_dvd_left b Q
  have hbm : b ∣ m := by
    dsimp [m]
    unfold allLagModulus
    exact dvd_pow_self b (by omega)
  have hrho : unitReduction hbm = coarseUnitReduction b ell := by
    unfold unitReduction coarseUnitReduction
    congr
  rw [lcmCarryChannel_sum_eq_compatible]
  rw [← hrho]
  have hzero := directCompatibleChannel_centered_sum_zero hdb hbm
    (unitReduction (Nat.gcd_dvd_right m Q) r) (allLagUnitTable b ell)
  simpa [m, d] using hzero

/-- An `lcm(m,Q)` channel has both equivalent totient-quotient counts. -/
theorem lcmCarryChannel_card
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)] [NeZero (Nat.gcd m Q)]
    (r : UnitClass Q) :
    Fintype.card (LcmCarryChannel (m := m) (Q := Q) r) =
        m.totient / (Nat.gcd m Q).totient ∧
      Fintype.card (LcmCarryChannel (m := m) (Q := Q) r) =
        (Nat.lcm m Q).totient / Q.totient := by
  constructor
  · rw [Fintype.card_congr (generalizedCarryChannelEquiv
      (m := m) (Q := Q) r)]
    exact unitReduction_fiber_card (Nat.gcd_dvd_left m Q)
      (unitReduction (Nat.gcd_dvd_right m Q) r)
  · exact unitReduction_fiber_card (Nat.dvd_lcm_right m Q) r

/-! ## Character gates and exact finite decomposition -/

/-- The primitive real sign modulo four in representative coordinates. -/
def chiFourSign (a : ℕ) : ℤ :=
  if a % 4 = 1 then 1 else if a % 4 = 3 then -1 else 0

/-- Exact conductor-four numerator for the centered decimal lag-one table. -/
def conductorFourCenteredNumerator : ℚ :=
  ∑ a ∈ reducedResidues 100,
    rationalCenteredTable 10 1 a * (chiFourSign a : ℚ)

/-- Integer numerator before coarse-fiber centering. -/
def conductorFourRawNumerator : ℤ :=
  ∑ a ∈ reducedResidues 100, allLagTable 10 1 a * chiFourSign a

/-- Conductor-four sign sum on one decimal coarse fiber. -/
def chiFourFiberSum (u : ℕ) : ℤ :=
  ∑ a ∈ tableFiber 10 1 u, chiFourSign a

set_option maxRecDepth 100000 in
theorem conductorFourRawNumerator_eq_zero : conductorFourRawNumerator = 0 := by
  decide

theorem chiFourFiberSum_eq_zero :
    ∀ u ∈ reducedResidues 10, chiFourFiberSum u = 0 := by
  decide

/-- A decimal unit modulo one hundred reduces to a decimal unit modulo ten. -/
theorem decimal_reduced_mod_ten_mem
    {a : ℕ} (ha : a ∈ reducedResidues 100) :
    a % 10 ∈ reducedResidues 10 := by
  rcases Finset.mem_filter.mp ha with ⟨haRange, haCop⟩
  rcases Finset.mem_Ico.mp haRange with ⟨ha1, ha100⟩
  have haCop10 : Nat.Coprime a 10 :=
    Nat.Coprime.of_dvd_right (by norm_num : 10 ∣ 100) haCop
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Ico.mpr
    constructor
    · have hne : a % 10 ≠ 0 := by
        intro hzero
        have hten : 10 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr hzero
        have hbad : Nat.Coprime 10 10 :=
          Nat.Coprime.of_dvd_left hten haCop10
        norm_num at hbad
      omega
    · exact Nat.mod_lt _ (by norm_num)
  · exact (ZMod.coprime_mod_iff_coprime a 10).2 haCop10

/-- Coarse-fiber centering contributes zero to the conductor-four sum. -/
theorem conductorFourCenteringCorrection_eq_zero :
    (∑ a ∈ reducedResidues 100,
      rationalFiberMean 10 1 (a % 10) * (chiFourSign a : ℚ)) = 0 := by
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := reducedResidues 100) (t := reducedResidues 10)
    (g := fun a => a % 10)
    (fun a ha => decimal_reduced_mod_ten_mem ha)
    (fun a => rationalFiberMean 10 1 (a % 10) * (chiFourSign a : ℚ))
  rw [← hgroup]
  apply Finset.sum_eq_zero
  intro u hu
  calc
    (∑ a ∈ reducedResidues 100 with a % 10 = u,
        rationalFiberMean 10 1 (a % 10) * (chiFourSign a : ℚ)) =
      rationalFiberMean 10 1 u *
        ∑ a ∈ tableFiber 10 1 u, (chiFourSign a : ℚ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr
          · rfl
          · intro a ha
            have hau := (Finset.mem_filter.mp ha).2
            rw [hau]
    _ = rationalFiberMean 10 1 u * (chiFourFiberSum u : ℚ) := by
      unfold chiFourFiberSum
      push_cast
      rfl
    _ = 0 := by rw [chiFourFiberSum_eq_zero u hu]; norm_num

/-- The conductor-four channel is exactly silent. -/
theorem conductorFourCenteredNumerator_eq_zero :
    conductorFourCenteredNumerator = 0 := by
  have hrawQ :
      (∑ a ∈ reducedResidues 100,
        (allLagTable 10 1 a : ℚ) * (chiFourSign a : ℚ)) = 0 := by
    calc
      _ = (conductorFourRawNumerator : ℚ) := by
        unfold conductorFourRawNumerator
        push_cast
        rfl
      _ = 0 := by rw [conductorFourRawNumerator_eq_zero]; norm_num
  unfold conductorFourCenteredNumerator rationalCenteredTable
  calc
    (∑ a ∈ reducedResidues 100,
        ((allLagTable 10 1 a : ℚ) - rationalFiberMean 10 1 (a % 10)) *
          (chiFourSign a : ℚ)) =
      (∑ a ∈ reducedResidues 100,
        (allLagTable 10 1 a : ℚ) * (chiFourSign a : ℚ)) -
      (∑ a ∈ reducedResidues 100,
        rationalFiberMean 10 1 (a % 10) * (chiFourSign a : ℚ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = 0 := by rw [hrawQ, conductorFourCenteringCorrection_eq_zero]; norm_num

/-- The conductor-four sign does not factor through reduction modulo ten. -/
theorem conductorFour_not_base_factored :
    1 % 10 = 11 % 10 ∧ chiFourSign 1 ≠ chiFourSign 11 := by
  decide

/-- Every finite weighted packet has the exact collision-character
decomposition used in the manuscript. -/
theorem exact_finite_character_decomposition
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (F : UnitClass q → ℂ) (residue : ι → UnitClass q)
    (weight : ι → ℂ) :
    ∑ i, F (residue i) * weight i =
      ∑ χ : Character q, collisionCoefficient F χ *
        ∑ i, χ (residue i).val * weight i :=
  finite_prime_packet_decomposition F residue weight

end NField.Alignment.GeneralNeutrality
