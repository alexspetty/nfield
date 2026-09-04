/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PhaseFilteredRamanujan

/-!
# Bin derangements and gate width

Reusable finite arithmetic for the Lean companion to
"Bin Derangements and the Gate Width Theorem".
-/

namespace NField.Alignment.BinDerangements

open scoped BigOperators
open ZMod
open NField.CollisionDefinition
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.PhaseFilteredRamanujan

/-! ## Conjugating digit intervals to congruence classes -/

/-- Euclidean division written with the transformed residue `[b r]_p`. -/
theorem digit_decomposition {b p : ℕ} (hbp : b < p) [NeZero p]
    (r : ZMod p) :
    b * r.val =
      p * digitBin b p r.val + ((b : ZMod p) * r).val := by
  have hmod : ((b : ZMod p) * r).val = (b * r.val) % p := by
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hbp]
  calc
    b * r.val = (b * r.val) % p + p * ((b * r.val) / p) :=
      (Nat.mod_add_div (b * r.val) p).symm
    _ = p * digitBin b p r.val + ((b : ZMod p) * r).val := by
      rw [hmod]
      unfold digitBin
      omega

/-- Multiplication by the base sends the interval digit bins to ordinary
congruence classes modulo the base. -/
theorem digit_eq_iff_transformed_mod {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    digitBin b p r.val = digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b =
        ((b : ZMod p) * s).val % b := by
  let dr := digitBin b p r.val
  let ds := digitBin b p s.val
  let xr := ((b : ZMod p) * r).val
  let xs := ((b : ZMod p) * s).val
  have hdr : b * r.val = p * dr + xr := digit_decomposition hbp r
  have hds : b * s.val = p * ds + xs := digit_decomposition hbp s
  have hrmod : p * dr + xr ≡ 0 [MOD b] := by
    rw [← hdr]
    simp [Nat.ModEq]
  have hsmod : p * ds + xs ≡ 0 [MOD b] := by
    rw [← hds]
    simp [Nat.ModEq]
  have hcop : Nat.Coprime b p := by
    exact ((hp.coprime_iff_not_dvd).mpr (by
      intro hpb
      have hle := Nat.le_of_dvd hb hpb
      omega)).symm
  constructor
  · intro hd
    change dr = ds at hd
    have hsum : p * dr + xr ≡ p * ds + xs [MOD b] :=
      hrmod.trans hsmod.symm
    rw [hd] at hsum
    have := hsum.add_left_cancel' (p * ds)
    simpa [Nat.ModEq] using this
  · intro hx
    have hxmod : xr ≡ xs [MOD b] := by
      simpa [Nat.ModEq] using hx
    have hsum : p * dr + xr ≡ p * ds + xs [MOD b] :=
      hrmod.trans hsmod.symm
    have hprod : p * dr ≡ p * ds [MOD b] :=
      hxmod.add_right_cancel hsum
    have hdmod : dr ≡ ds [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hprod
    have hdrlt : dr < b := digitBin_lt_base hb hp.pos r.val_lt
    have hdslt : ds < b := digitBin_lt_base hb hp.pos s.val_lt
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hdrlt,
      Nat.mod_eq_of_lt hdslt] using hdmod

/-- The manuscript's collision congruence count after the base permutation. -/
def transformedCollisionCount (b p : ℕ) [NeZero p]
    (g : ZMod p) : ℕ :=
  ∑ x : ZMod p,
    if x ≠ 0 ∧ x.val % b = (g * x).val % b then 1 else 0

/-- The intrinsic digit collision count is exactly the transformed congruence
count. -/
theorem collisionCount_eq_transformedCollisionCount {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) (hg : g ≠ 0) :
    collisionCount (primeDigitWord b p hb hp.pos) g =
      transformedCollisionCount b p g := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hbase : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast_of_lt hbp, hb.ne']
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (b : ZMod p) hbase
  let transformedTerm : ZMod p → ℕ := fun x =>
    if x ≠ 0 ∧ x.val % b = (g * x).val % b then 1 else 0
  calc
    collisionCount (primeDigitWord b p hb hp.pos) g =
        ∑ r : ZMod p,
          if r ≠ 0 ∧
              ((b : ZMod p) * r).val % b =
                ((b : ZMod p) * (g * r)).val % b
          then 1 else 0 := by
      unfold collisionCount
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r = 0
      · simp [hr, primeDigitWord_zero]
      · have hgr : g * r ≠ 0 := mul_ne_zero hg hr
        simp [primeDigitWord, hr, hgr, Fin.ext_iff,
          digit_eq_iff_transformed_mod hb hp hbp]
    _ = ∑ x : ZMod p, transformedTerm x := by
      apply Fintype.sum_equiv e
      intro r
      simp only [transformedTerm, e, Equiv.mulLeft₀_apply]
      rw [show g * ((b : ZMod p) * r) =
          (b : ZMod p) * (g * r) by ring]
      simp [hbase]
    _ = transformedCollisionCount b p g := rfl

/-! ## The gate parameter -/

/-- The least nonnegative representative of `b (1-g)⁻¹`. -/
def gateParameter (b p : ℕ) [NeZero p] (g : ZMod p) : ℕ :=
  ((b : ZMod p) * (1 - g)⁻¹).val

/-- The gate parameter satisfies the manuscript's defining congruence. -/
theorem gateParameter_mul_one_sub {b p : ℕ}
    (hp : Nat.Prime p) [NeZero p] {g : ZMod p} (hg1 : g ≠ 1) :
    (gateParameter b p g : ZMod p) * (1 - g) = (b : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [gateParameter, ZMod.natCast_zmod_val]
  field_simp

/-- A nonzero base and a nonidentity multiplier give a positive gate
parameter. -/
theorem gateParameter_pos {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg1 : g ≠ 1) :
    0 < gateParameter b p g := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  unfold gateParameter
  rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
  exact mul_ne_zero (by
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast_of_lt hbp, hb.ne'])
    (inv_ne_zero (sub_ne_zero.mpr hg1.symm))

theorem gateParameter_lt {b p : ℕ} [NeZero p] (g : ZMod p) :
    gateParameter b p g < p :=
  ZMod.val_lt _

/-- The omitted parameter value `b` would force the multiplier to be zero. -/
theorem gateParameter_ne_base {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    gateParameter b p g ≠ b := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hc
  have hparam := gateParameter_mul_one_sub (b := b) hp hg1
  rw [hc] at hparam
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast_of_lt hbp, hb.ne']
  have hparam' : (b : ZMod p) * (1 - g) = (b : ZMod p) * 1 := by
    simpa using hparam
  have hone : (1 - g : ZMod p) = 1 := mul_left_cancel₀ hb0 hparam'
  have : g = 0 := sub_eq_self.mp hone
  exact hg0 this

/-! ## The two sides of the zero gate -/

/-- In the increasing-quotient case, the parameter identity forces the
positive representative `x + m c` to vanish modulo `p`. -/
theorem increasing_quotient_obstruction {p : ℕ} [NeZero p]
    {b c g x y : ZMod p} {m : ℕ}
    (hparam : c * (1 - g) = b) (hy : y = g * x)
    (hshift : y = x + (m * b.val : ℕ)) :
    b * (x + (m : ZMod p) * c) = 0 := by
  rw [show ((m * b.val : ℕ) : ZMod p) = (m : ZMod p) * b by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]] at hshift
  linear_combination -(hparam * x - c * hy + c * hshift)

/-- In the decreasing-quotient case, the parameter identity forces the
positive representative `x - n c` to vanish modulo `p`. -/
theorem decreasing_quotient_obstruction {p : ℕ} [NeZero p]
    {b c g x y : ZMod p} {n : ℕ}
    (hparam : c * (1 - g) = b) (hy : y = g * x)
    (hshift : x = y + (n * b.val : ℕ)) :
    b * (x - (n : ZMod p) * c) = 0 := by
  rw [show ((n * b.val : ℕ) : ZMod p) = (n : ZMod p) * b by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]] at hshift
  linear_combination -(hparam * x - c * hy - c * hshift)

/-- Parameters strictly below the base give no transformed congruence
collisions.  This is the manuscript's zero-side argument with both quotient
orders made explicit. -/
theorem transformedCollisionCount_eq_zero_of_parameter_lt {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1)
    (hc_lt : gateParameter b p g < b) :
    transformedCollisionCount b p g = 0 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let c := gateParameter b p g
  have hcpos : 0 < c := gateParameter_pos hb hp hbp hg1
  have hcltp : c < p := gateParameter_lt g
  have hparam : (c : ZMod p) * (1 - g) = (b : ZMod p) :=
    gateParameter_mul_one_sub hp hg1
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast_of_lt hbp, hb.ne']
  unfold transformedCollisionCount
  rw [Finset.sum_eq_zero_iff]
  intro x _
  by_cases hcollision : x ≠ 0 ∧ x.val % b = (g * x).val % b
  · have hx0 := hcollision.1
    have hy0 : g * x ≠ 0 := mul_ne_zero hg0 hx0
    have hxpos : 0 < x.val := ZMod.val_pos.mpr hx0
    have hypos : 0 < (g * x).val := ZMod.val_pos.mpr hy0
    let qx := x.val / b
    let qy := (g * x).val / b
    by_cases hq : qx ≤ qy
    · let m := qy - qx
      have hshiftNat : (g * x).val = x.val + m * b := by
        have hxdiv : x.val % b + b * qx = x.val := by
          simpa [qx] using Nat.mod_add_div x.val b
        have hydiv : (g * x).val % b + b * qy = (g * x).val := by
          simpa [qy] using Nat.mod_add_div (g * x).val b
        have hqm : qx + m = qy := by
          dsimp [m]
          omega
        calc
          (g * x).val = (g * x).val % b + b * qy := hydiv.symm
          _ = x.val % b + b * (qx + m) := by
            rw [← hcollision.2, hqm]
          _ = (x.val % b + b * qx) + m * b := by ring
          _ = x.val + m * b := by rw [hxdiv]
      have hshiftZ : g * x =
          x + ((m * (b : ZMod p).val : ℕ) : ZMod p) := by
        rw [ZMod.val_natCast_of_lt hbp]
        calc
          g * x = ((g * x).val : ZMod p) :=
            (ZMod.natCast_zmod_val (g * x)).symm
          _ = ((x.val + m * b : ℕ) : ZMod p) := by rw [hshiftNat]
          _ = x + ((m * b : ℕ) : ZMod p) := by
            rw [Nat.cast_add, ZMod.natCast_zmod_val]
      have hobs := increasing_quotient_obstruction
        (p := p) (b := (b : ZMod p)) (c := (c : ZMod p))
        (g := g) (x := x) (y := g * x) (m := m)
        hparam rfl hshiftZ
      have hzero : x + (m : ZMod p) * (c : ZMod p) = 0 :=
        mul_left_cancel₀ hb0 (by simpa using hobs)
      let z := x.val + m * c
      have hzcast : (z : ZMod p) = 0 := by
        dsimp [z]
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
        exact hzero
      have hzdvd : p ∣ z := (ZMod.natCast_eq_zero_iff z p).mp hzcast
      have hzpos : 0 < z := by
        dsimp [z]
        omega
      have hzlt : z < p := by
        have hmle : m * c ≤ m * b :=
          Nat.mul_le_mul_left m (Nat.le_of_lt hc_lt)
        have hylt := (g * x).val_lt
        dsimp [z]
        omega
      have hpz := Nat.le_of_dvd hzpos hzdvd
      omega
    · have hq' : qy < qx := by omega
      let n := qx - qy
      have hshiftNat : x.val = (g * x).val + n * b := by
        have hxdiv : x.val % b + b * qx = x.val := by
          simpa [qx] using Nat.mod_add_div x.val b
        have hydiv : (g * x).val % b + b * qy = (g * x).val := by
          simpa [qy] using Nat.mod_add_div (g * x).val b
        have hqn : qy + n = qx := by
          dsimp [n]
          omega
        calc
          x.val = x.val % b + b * qx := hxdiv.symm
          _ = (g * x).val % b + b * (qy + n) := by
            rw [hcollision.2, hqn]
          _ = ((g * x).val % b + b * qy) + n * b := by ring
          _ = (g * x).val + n * b := by rw [hydiv]
      have hshiftZ : x =
          g * x + ((n * (b : ZMod p).val : ℕ) : ZMod p) := by
        rw [ZMod.val_natCast_of_lt hbp]
        calc
          x = (x.val : ZMod p) := (ZMod.natCast_zmod_val x).symm
          _ = (((g * x).val + n * b : ℕ) : ZMod p) := by rw [hshiftNat]
          _ = g * x + ((n * b : ℕ) : ZMod p) := by
            rw [Nat.cast_add, ZMod.natCast_zmod_val]
      have hobs := decreasing_quotient_obstruction
        (p := p) (b := (b : ZMod p)) (c := (c : ZMod p))
        (g := g) (x := x) (y := g * x) (n := n)
        hparam rfl hshiftZ
      have hzero : x - (n : ZMod p) * (c : ZMod p) = 0 :=
        mul_left_cancel₀ hb0 (by simpa using hobs)
      have hnc : n * c ≤ x.val := by
        have hnle : n * c ≤ n * b :=
          Nat.mul_le_mul_left n (Nat.le_of_lt hc_lt)
        omega
      let z := x.val - n * c
      have hzcast : (z : ZMod p) = 0 := by
        dsimp [z]
        rw [Nat.cast_sub hnc, Nat.cast_mul, ZMod.natCast_zmod_val]
        exact hzero
      have hzdvd : p ∣ z := (ZMod.natCast_eq_zero_iff z p).mp hzcast
      have hzpos : 0 < z := by
        have hnle : n * c ≤ n * b :=
          Nat.mul_le_mul_left n (Nat.le_of_lt hc_lt)
        have hnclt : n * c < x.val := by omega
        exact Nat.sub_pos_of_lt hnclt
      have hzlt : z < p := by
        exact lt_of_le_of_lt (Nat.sub_le x.val (n * c)) x.val_lt
      have hpz := Nat.le_of_dvd hzpos hzdvd
      omega
  · simp [hcollision]

/-- Parameters strictly above the base give an explicit transformed
congruence collision. -/
theorem transformedCollisionCount_pos_of_base_lt_parameter {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    {g : ZMod p} (hg1 : g ≠ 1)
    (hc_gt : b < gateParameter b p g) :
    0 < transformedCollisionCount b p g := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let c := gateParameter b p g
  have hcpos : 0 < c := by omega
  have hcltp : c < p := gateParameter_lt g
  have hparam : (c : ZMod p) * (1 - g) = (b : ZMod p) :=
    gateParameter_mul_one_sub hp hg1
  let xn := p - c
  let yn := xn + b
  have hxnpos : 0 < xn := by dsimp [xn]; omega
  have hxnlt : xn < p := by dsimp [xn]; omega
  have hynpos : 0 < yn := by dsimp [yn]; omega
  have hynlt : yn < p := by dsimp [yn, xn]; omega
  let x : ZMod p := xn
  have hxval : x.val = xn := ZMod.val_natCast_of_lt hxnlt
  have hxclass : x = -(c : ZMod p) := by
    dsimp [x, xn]
    rw [Nat.cast_sub (Nat.le_of_lt hcltp)]
    simp
  have hmul : g * (-(c : ZMod p)) = (b : ZMod p) - c := by
    linear_combination hparam
  have hyclass : (yn : ZMod p) = (b : ZMod p) - c := by
    dsimp [yn, xn]
    rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hcltp)]
    simp
    ring
  have hgx : g * x = (yn : ZMod p) := by
    rw [hxclass, hmul, hyclass]
  have hyval : (g * x).val = yn := by
    rw [hgx, ZMod.val_natCast_of_lt hynlt]
  have hx0 : x ≠ 0 := by
    rw [← ZMod.val_ne_zero, hxval]
    exact hxnpos.ne'
  have hmod : x.val % b = (g * x).val % b := by
    rw [hxval, hyval]
    dsimp [yn]
    exact (Nat.add_mod_right xn b).symm
  unfold transformedCollisionCount
  apply Finset.sum_pos'
  · intro z _
    split <;> simp
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [hx0, hmod]

/-- For a nonzero, nonidentity multiplier, collision freedom is exactly the
strict lower side of the gate parameter. -/
theorem transformedCollisionCount_eq_zero_iff_parameter_lt {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    transformedCollisionCount b p g = 0 ↔ gateParameter b p g < b := by
  constructor
  · intro hzero
    have hcne := gateParameter_ne_base hb hp hbp hg0 hg1
    rcases lt_or_gt_of_ne hcne with hlt | hgt
    · exact hlt
    · have hpos := transformedCollisionCount_pos_of_base_lt_parameter
        hb hp hg1 hgt
      omega
  · exact transformedCollisionCount_eq_zero_of_parameter_lt
      hb hp hbp hg0 hg1

/-- The central zero-gate criterion for the intrinsic prime digit word. -/
theorem collisionCount_eq_zero_iff_parameter_lt {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p hb hp.pos) g = 0 ↔
      gateParameter b p g < b := by
  rw [collisionCount_eq_transformedCollisionCount hb hp hbp g hg0]
  exact transformedCollisionCount_eq_zero_iff_parameter_lt
    hb hp hbp hg0 hg1

/-! ## The explicit deranging family -/

/-- The manuscript's displayed multiplier `-u/(b-u)`. -/
def derangingMultiplier (b p u : ℕ) : ZMod p :=
  -(u : ZMod p) * ((b - u : ℕ) : ZMod p)⁻¹

/-- The finite set obtained from all parameters `1 ≤ u < b`. -/
def derangingFamily (b p : ℕ) : Finset (ZMod p) :=
  (Finset.Ico 1 b).image (derangingMultiplier b p)

/-- The displayed multiplier has parameter `c=b-u`. -/
theorem derangingMultiplier_parameter_identity {b p u : ℕ}
    (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    (((b - u : ℕ) : ZMod p) *
        (1 - derangingMultiplier b p u)) = (b : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcpos : 0 < b - u := Nat.sub_pos_of_lt hub
  have hcltp : b - u < p := lt_of_lt_of_le (Nat.sub_lt (by omega) hu0)
    (Nat.le_of_lt hbp)
  have hc0 : ((b - u : ℕ) : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  unfold derangingMultiplier
  rw [mul_sub, mul_one]
  field_simp
  rw [Nat.cast_sub (Nat.le_of_lt hub)]
  ring

/-- Every displayed multiplier is nonzero. -/
theorem derangingMultiplier_ne_zero {b p u : ℕ}
    (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    derangingMultiplier b p u ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hultp : u < p := lt_trans hub hbp
  have hupos : (u : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hultp]
    exact hu0.ne'
  have hcpos : 0 < b - u := Nat.sub_pos_of_lt hub
  have hcltp : b - u < p := lt_trans (Nat.sub_lt (by omega) hu0) hbp
  have hc0 : ((b - u : ℕ) : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  exact mul_ne_zero (neg_ne_zero.mpr hupos) (inv_ne_zero hc0)

/-- Every displayed multiplier is different from the identity. -/
theorem derangingMultiplier_ne_one {b p u : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    derangingMultiplier b p u ≠ 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hg1
  have hparam := derangingMultiplier_parameter_identity hp hbp hu0 hub
  rw [hg1, sub_self, mul_zero] at hparam
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hbp]
    exact hb.ne'
  exact hb0 hparam.symm

/-- A parameter identity determines the least representative used by
`gateParameter`. -/
theorem gateParameter_eq_of_identity {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] {g : ZMod p}
    (hc_lt : c < p) (hg1 : g ≠ 1)
    (hparam : (c : ZMod p) * (1 - g) = (b : ZMod p)) :
    gateParameter b p g = c := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hgate := gateParameter_mul_one_sub (b := b) hp hg1
  have hsub0 : (1 - g : ZMod p) ≠ 0 := sub_ne_zero.mpr hg1.symm
  have hcast : (gateParameter b p g : ZMod p) = (c : ZMod p) := by
    apply mul_right_cancel₀ hsub0
    exact hgate.trans hparam.symm
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast_of_lt (gateParameter_lt g),
    ZMod.val_natCast_of_lt hc_lt] using hval

/-- Every member of the explicit family is collision-free. -/
theorem collisionCount_derangingMultiplier_eq_zero {b p u : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    collisionCount (primeDigitWord b p hb hp.pos)
        (derangingMultiplier b p u) = 0 := by
  have hg0 := derangingMultiplier_ne_zero hp hbp hu0 hub
  have hg1 := derangingMultiplier_ne_one hb hp hbp hu0 hub
  rw [collisionCount_eq_zero_iff_parameter_lt hb hp hbp hg0 hg1]
  have hcpos : 0 < b - u := Nat.sub_pos_of_lt hub
  have hcltp : b - u < p := lt_trans (Nat.sub_lt (by omega) hu0) hbp
  rw [gateParameter_eq_of_identity hp hcltp hg1
    (derangingMultiplier_parameter_identity hp hbp hu0 hub)]
  omega

/-- A collision-free nonzero multiplier is one of the displayed
`-u/(b-u)` values. -/
theorem collisionFree_mem_derangingFamily {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0)
    (hzero : collisionCount
      (primeDigitWord b p (by omega) hp.pos) g = 0) :
    g ∈ derangingFamily b p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpone : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hg1 : g ≠ 1 := by
    intro hg
    subst g
    rw [collisionCount_one, prime_assignedMass (by omega) hp.pos] at hzero
    omega
  have hc_lt := (collisionCount_eq_zero_iff_parameter_lt
    (b := b) (p := p) (by omega) hp hbp hg0 hg1).mp hzero
  let c := gateParameter b p g
  have hcpos : 0 < c := gateParameter_pos (by omega) hp hbp hg1
  let u := b - c
  have hu0 : 0 < u := Nat.sub_pos_of_lt hc_lt
  have hub : u < b := by dsimp [u]; omega
  have huc : b - u = c := by dsimp [u]; omega
  have hcZ0 : (c : ZMod p) ≠ 0 := by
    have hcltp := gateParameter_lt (b := b) g
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  have hparam := gateParameter_mul_one_sub (b := b) hp hg1
  change (c : ZMod p) * (1 - g) = (b : ZMod p) at hparam
  have htargetParam :
      (c : ZMod p) * (1 - derangingMultiplier b p u) = (b : ZMod p) := by
    rw [← huc]
    exact derangingMultiplier_parameter_identity hp hbp hu0 hub
  have hgeq : g = derangingMultiplier b p u := by
    apply sub_right_inj.mp
    apply mul_left_cancel₀ hcZ0
    exact hparam.trans htargetParam.symm
  unfold derangingFamily
  rw [Finset.mem_image]
  exact ⟨u, Finset.mem_Ico.mpr ⟨hu0, hub⟩, hgeq.symm⟩

/-- The intrinsic collision-free set is exactly the displayed family. -/
theorem mem_derangingFamily_iff {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) :
    g ∈ derangingFamily b p ↔
      g ≠ 0 ∧ collisionCount
        (primeDigitWord b p (by omega) hp.pos) g = 0 := by
  constructor
  · intro hg
    rw [derangingFamily, Finset.mem_image] at hg
    obtain ⟨u, hu, rfl⟩ := hg
    have hu' := Finset.mem_Ico.mp hu
    exact ⟨derangingMultiplier_ne_zero hp hbp (by omega) hu'.2,
      collisionCount_derangingMultiplier_eq_zero
        (by omega) hp hbp (by omega) hu'.2⟩
  · rintro ⟨hg0, hzero⟩
    exact collisionFree_mem_derangingFamily hb2 hp hbp hg0 hzero

/-- The gate parameter of the displayed multiplier is exactly `b-u`. -/
theorem gateParameter_derangingMultiplier {b p u : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    gateParameter b p (derangingMultiplier b p u) = b - u := by
  apply gateParameter_eq_of_identity hp
  · exact lt_trans (Nat.sub_lt (by omega) hu0) hbp
  · exact derangingMultiplier_ne_one hb hp hbp hu0 hub
  · exact derangingMultiplier_parameter_identity hp hbp hu0 hub

/-- The displayed parametrization has no repetitions. -/
theorem derangingMultiplier_injOn {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    Set.InjOn (derangingMultiplier b p) (Finset.Ico 1 b) := by
  intro u hu v hv huv
  have hu' := Finset.mem_Ico.mp hu
  have hv' := Finset.mem_Ico.mp hv
  have hparam := congrArg (gateParameter b p) huv
  rw [gateParameter_derangingMultiplier hb hp hbp (by omega) hu'.2,
    gateParameter_derangingMultiplier hb hp hbp (by omega) hv'.2] at hparam
  omega

/-- The exact gate width is `b-1`, independently of the prime. -/
theorem derangingFamily_card {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (derangingFamily b p).card = b - 1 := by
  unfold derangingFamily
  rw [Finset.card_image_iff.mpr (derangingMultiplier_injOn hb hp hbp)]
  simp

/-- The parameters `u` and `b-u` give inverse multipliers. -/
theorem derangingMultiplier_complement {b p u : ℕ}
    (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    derangingMultiplier b p (b - u) =
      (derangingMultiplier b p u)⁻¹ := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hultp : u < p := lt_trans hub hbp
  have hcpos : 0 < b - u := Nat.sub_pos_of_lt hub
  have hcltp : b - u < p := lt_trans (Nat.sub_lt (by omega) hu0) hbp
  have huZ : (u : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hultp]
    exact hu0.ne'
  have hcZ : ((b - u : ℕ) : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  unfold derangingMultiplier
  rw [Nat.sub_sub_self (Nat.le_of_lt hub)]
  field_simp

/-! ## Collision mass -/

/-- Summing collision counts over all multipliers counts every ordered
same-bin pair exactly once. -/
theorem collisionCount_sum_rule {p κ : ℕ}
    (hp : Nat.Prime p) [NeZero p]
    (word : ZMod p → Option (Fin κ)) (hzero : word 0 = none) :
    ∑ g : ZMod p, collisionCount word g = binSquareMass word := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hinner (r : ZMod p) :
      (∑ g : ZMod p,
          if word r = word (g * r) ∧ word r ≠ none then 1 else 0) =
        match word r with
        | none => 0
        | some d => (binSet word d).card := by
    cases hrword : word r with
    | none => simp
    | some d =>
        have hr0 : r ≠ 0 := by
          intro hr
          subst r
          rw [hzero] at hrword
          contradiction
        let e : ZMod p ≃ ZMod p := Equiv.mulRight₀ r hr0
        calc
          (∑ g : ZMod p,
              if some d = word (g * r) ∧ some d ≠ none then 1 else 0) =
              ∑ s : ZMod p,
                if some d = word s ∧ some d ≠ none then 1 else 0 := by
            apply Fintype.sum_equiv e
            intro g
            rfl
          _ = (binSet word d).card := by
            rw [Finset.sum_boole]
            have hset :
                (Finset.univ.filter fun s : ZMod p =>
                    some d = word s ∧ some d ≠ none) =
                  binSet word d := by
              ext s
              simp [binSet, eq_comm]
            rw [hset]
            norm_num
  unfold collisionCount
  rw [Finset.sum_comm]
  simp_rw [hinner]
  unfold binSquareMass
  calc
    (∑ r : ZMod p,
        match word r with
        | none => 0
        | some d => (binSet word d).card) =
      ∑ r : ZMod p, ∑ d : Fin κ,
        if word r = some d then (binSet word d).card else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          cases hr : word r with
          | none => simp
          | some d => simp
    _ = ∑ d : Fin κ, ∑ r : ZMod p,
        if word r = some d then (binSet word d).card else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ d : Fin κ, (binSet word d).card ^ 2 := by
          apply Finset.sum_congr rfl
          intro d _
          calc
            (∑ r : ZMod p,
                if word r = some d then (binSet word d).card else 0) =
              (∑ r : ZMod p, if word r = some d then 1 else 0) *
                (binSet word d).card := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro r _
                  split <;> simp_all
            _ = (binSet word d).card * (binSet word d).card := by
                  rw [Finset.sum_boole]
                  rfl
            _ = (binSet word d).card ^ 2 := by ring

/-- The sum rule specialized to the intrinsic prime digit word. -/
theorem prime_collisionCount_sum_rule {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p] :
    ∑ g : ZMod p,
        collisionCount (primeDigitWord b p hb hp.pos) g =
      digitBinSquareSum b p := by
  rw [collisionCount_sum_rule hp _ (primeDigitWord_zero b p hb hp.pos)]
  unfold binSquareMass digitBinSquareSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  simp [hd, primeDigitWord_bin_card hb hp.pos]

/-! ## Exact Euclidean mean algebra -/

/-- Subtracting the identity contribution from a two-length bin-square mass
gives the manuscript's constructive collision total. -/
theorem constructive_collision_total {b p Q R : ℕ}
    (hQ : 1 ≤ Q) (hdivision : p - 1 = b * Q + R) :
    (b * Q ^ 2 + R * (2 * Q + 1)) - (p - 1) =
      Q * (b * (Q - 1) + 2 * R) := by
  have hle : p - 1 ≤ b * Q ^ 2 + R * (2 * Q + 1) := by
    rw [hdivision]
    nlinarith
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
  rw [Nat.sub_eq_iff_eq_add hle, hdivision]
  simp
  ring

/-- The exact constructive mean, stated over rationals so division is total. -/
theorem constructive_collision_mean {b p Q R : ℕ}
    (hQ : 1 ≤ Q) (hdivision : p - 1 = b * Q + R)
    (hpositive : 0 < b * (Q - 1) + R) :
    ((b * Q ^ 2 + R * (2 * Q + 1) - (p - 1) : ℕ) : ℚ) /
        ((b * (Q - 1) + R : ℕ) : ℚ) =
      (Q * (b * (Q - 1) + 2 * R) : ℕ) /
        ((b * (Q - 1) + R : ℕ) : ℚ) := by
  have hdenom : (b * (Q - 1) + R : ℚ) ≠ 0 := by
    exact_mod_cast hpositive.ne'
  rw [constructive_collision_total hQ hdivision]

/-- Throughout the first constructive range, the exact mean is two. -/
theorem constructive_collision_mean_eq_two_of_Q_one {b p R : ℕ}
    (hdivision : p - 1 = b + R) (hR : 0 < R) :
    ((b + R * 3 - (p - 1) : ℕ) : ℚ) / R = 2 := by
  have hnum : b + R * 3 - (p - 1) = 2 * R := by
    rw [hdivision]
    omega
  rw [hnum]
  push_cast
  field_simp

/-! ## Full-orbit readout and exact finite certificates -/

/-- On a full cyclic enumeration of nonzero residues, the zero lags are
exactly the lower gate parameters.  A primitive-root proof supplies the orbit
and motion hypotheses used here. -/
theorem fullOrbitAutocorrelation_eq_zero_iff_parameter_lt
    {G : Type*} [Fintype G] [AddCommGroup G]
    {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (orbit : G ≃ NonzeroResidue p) (lag : G) (g : ZMod p)
    (hmotion : ∀ t, (orbit (t + lag)).val = g * (orbit t).val)
    (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    fullOrbitAutocorrelation (primeDigitWord b p hb hp.pos) orbit lag = 0 ↔
      gateParameter b p g < b := by
  rw [fullOrbitAutocorrelation_eq_collision
    (primeDigitWord b p hb hp.pos) orbit lag g
    (primeDigitWord_zero b p hb hp.pos) hmotion]
  rw [multiplicativeCollision_eq_collisionCount]
  norm_cast
  exact collisionCount_eq_zero_iff_parameter_lt hb hp hbp hg0 hg1

/-- Exact decimal prime-thirteen deranging family from the displayed formula. -/
theorem decimal_thirteen_deranging_family :
    derangingFamily 10 13 =
      ({2, 3, 4, 5, 7, 8, 9, 10, 12} : Finset (ZMod 13)) := by
  have h2 : (2 : ZMod 13)⁻¹ = 7 :=
    ZMod.inv_eq_of_mul_eq_one 13 2 7 (by decide)
  have h3 : (3 : ZMod 13)⁻¹ = 9 :=
    ZMod.inv_eq_of_mul_eq_one 13 3 9 (by decide)
  have h4 : (4 : ZMod 13)⁻¹ = 10 :=
    ZMod.inv_eq_of_mul_eq_one 13 4 10 (by decide)
  have h5 : (5 : ZMod 13)⁻¹ = 8 :=
    ZMod.inv_eq_of_mul_eq_one 13 5 8 (by decide)
  have h6 : (6 : ZMod 13)⁻¹ = 11 :=
    ZMod.inv_eq_of_mul_eq_one 13 6 11 (by decide)
  have h7 : (7 : ZMod 13)⁻¹ = 2 :=
    ZMod.inv_eq_of_mul_eq_one 13 7 2 (by decide)
  have h8 : (8 : ZMod 13)⁻¹ = 5 :=
    ZMod.inv_eq_of_mul_eq_one 13 8 5 (by decide)
  have h9 : (9 : ZMod 13)⁻¹ = 3 :=
    ZMod.inv_eq_of_mul_eq_one 13 9 3 (by decide)
  ext a
  simp only [derangingFamily, Finset.mem_image, Finset.mem_Ico,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, ⟨hu0, hu10⟩, rfl⟩
    interval_cases u <;>
      norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9] <;>
      decide
  · intro ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨7, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨2, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨9, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨6, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨3, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨4, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨8, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨1, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩
    · exact ⟨5, by norm_num,
        by norm_num [derangingMultiplier, h2, h3, h4, h5, h6, h7, h8, h9]; decide⟩

/-- The first constructive multiplier at thirteen has collision count two. -/
theorem decimal_thirteen_collision_six :
    collisionCount decimalThirteenDigitWord 6 = 2 := by
  change collisionCount
    (primeDigitWord 10 13 (by norm_num) (by norm_num)) 6 = 2
  rw [collisionCount_eq_transformedCollisionCount
    (b := 10) (p := 13) (g := 6)
    (by norm_num) (by norm_num) (by norm_num) (by decide)]
  norm_num [transformedCollisionCount]; decide

/-- The second constructive multiplier at thirteen has collision count two. -/
theorem decimal_thirteen_collision_eleven :
    collisionCount decimalThirteenDigitWord 11 = 2 := by
  change collisionCount
    (primeDigitWord 10 13 (by norm_num) (by norm_num)) 11 = 2
  rw [collisionCount_eq_transformedCollisionCount
    (b := 10) (p := 13) (g := 11)
    (by norm_num) (by norm_num) (by norm_num) (by decide)]
  norm_num [transformedCollisionCount]; decide

end NField.Alignment.BinDerangements
