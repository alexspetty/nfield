/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-!
# Lifted-boundary invisibility

A block lift repeats each lower-level cell across a fixed-length block. Its
cyclic boundary can occur only at block endpoints. When a prime divides the
block length, every surviving endpoint is a nonunit and every primitive
character transform vanishes.
-/

namespace NField.Alignment.LiftedBoundaryInvisibility

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra

/-- Decrementing a non-boundary index does not change its block quotient. -/
theorem pred_div_eq_div_of_not_dvd
    {a L : ℕ} (hL : 0 < L) (ha : 0 < a) (hnot : ¬L ∣ a) :
    (a - 1) / L = a / L := by
  have hr : a % L ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnot
  have hrpos : 0 < a % L := Nat.pos_of_ne_zero hr
  have hrlt : a % L < L := Nat.mod_lt _ hL
  have hdecomp := Nat.mod_add_div a L
  have haeq : a - 1 = (a % L - 1) + L * (a / L) := by omega
  rw [haeq, Nat.add_mul_div_left _ _ hL]
  have hz : (a % L - 1) / L = 0 := Nat.div_eq_of_lt (by omega)
  rw [hz, zero_add]

/-- Dividing the predecessor of a positive block endpoint recovers the
predecessor of the block index. -/
theorem pred_mul_div
    {L y : ℕ} (hL : 0 < L) (hy : 0 < y) :
    (L * y - 1) / L = y - 1 := by
  have hydec : y = (y - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hsplit : L * y - 1 = L * (y - 1) + (L - 1) := by
    calc
      L * y - 1 = L * (y - 1) + L - 1 := by
        rw [hydec, mul_add]
        simp
      _ = L * (y - 1) + (L - 1) := by omega
  rw [hsplit, Nat.mul_add_div hL, Nat.div_eq_of_lt (by omega), add_zero]

/-- Block lift of a cyclic lower-level weight. -/
noncomputable def blockLiftWeight
    {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (h : ZMod q → ℂ) (x : ZMod (q * L)) : ℂ :=
  h ((x.val / L : ℕ) : ZMod q)

/-- Title: `Boundary of a block lift at dilated endpoints`.

The boundary of a block lift at every dilated endpoint is exactly the
lower-level signed boundary. Together with vanishing off dilated endpoints,
this is the finite pushforward identity for the complete boundary chain. -/
theorem blockLiftBoundary_at_dilated_point
    {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 2 ≤ q) (hL : 0 < L) (h : ZMod q → ℂ)
    (y : ZMod q) :
    signedBoundary (blockLiftWeight h)
        ((L * y.val : ℕ) : ZMod (q * L)) =
      signedBoundary h y := by
  letI : Fact (1 < q) := ⟨by omega⟩
  letI : Fact (1 < q * L) := ⟨by nlinarith⟩
  have hylt : L * y.val < q * L := by
    nlinarith [y.val_lt]
  have hxval :
      (((L * y.val : ℕ) : ZMod (q * L))).val = L * y.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hylt]
  by_cases hy0 : y.val = 0
  · have hy : y = 0 := (ZMod.val_eq_zero y).mp hy0
    subst y
    have htop : 0 < q * L := Nat.mul_pos (by omega) hL
    have hneg :
        (-1 : ZMod (q * L)).val = q * L - 1 := by
      have heq : q * L = (q * L - 1) + 1 :=
        (Nat.sub_add_cancel (by omega)).symm
      rw [heq]
      exact ZMod.val_neg_one (q * L - 1)
    have hquot : (q * L - 1) / L = q - 1 := by
      rw [Nat.mul_comm]
      exact pred_mul_div hL (by omega)
    unfold signedBoundary blockLiftWeight
    simp only [ZMod.val_zero, mul_zero, Nat.zero_div, Nat.cast_zero, zero_sub]
    change h ((((-1 : ZMod (q * L)).val / L : ℕ) : ZMod q)) -
        h 0 = h (-1) - h 0
    rw [hneg, hquot]
    congr 2
    have hvalneg : (-1 : ZMod q).val = q - 1 := by
      have hqeq : q = (q - 1) + 1 :=
        (Nat.sub_add_cancel (by omega)).symm
      rw [hqeq]
      exact ZMod.val_neg_one (q - 1)
    calc
      ((q - 1 : ℕ) : ZMod q) =
          (((-1 : ZMod q).val : ℕ) : ZMod q) := by rw [hvalneg]
      _ = -1 := ZMod.natCast_zmod_val _
  · have hypos : 0 < y.val := Nat.pos_of_ne_zero hy0
    have hxpos : 0 < L * y.val := Nat.mul_pos hL hypos
    let x : ZMod (q * L) := (L * y.val : ℕ)
    have hxval' : x.val = L * y.val := hxval
    have honeval : (1 : ZMod (q * L)).val = 1 := ZMod.val_one (q * L)
    have hxprev : (x - 1).val = L * y.val - 1 := by
      rw [ZMod.val_sub (by rw [honeval]; omega), hxval', honeval]
    have hyprev : (y - 1).val = y.val - 1 := by
      rw [ZMod.val_sub (by rw [ZMod.val_one]; omega), ZMod.val_one]
    have hdiv : L * y.val / L = y.val := Nat.mul_div_right y.val hL
    unfold signedBoundary blockLiftWeight
    change h (((x - 1).val / L : ℕ) : ZMod q) -
        h ((x.val / L : ℕ) : ZMod q) =
      h (y - 1) - h y
    rw [hxprev, hxval', pred_mul_div hL hypos, hdiv]
    rw [← hyprev, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- Title: `Vanishing away from dilated endpoints`.

A block-lift boundary vanishes away from indices divisible by the block length. -/
theorem blockLiftBoundary_zero_off_dilated_support
    {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 2 ≤ q) (hL : 0 < L) (h : ZMod q → ℂ)
    (x : ZMod (q * L)) (hx : ¬L ∣ x.val) :
    signedBoundary (blockLiftWeight h) x = 0 := by
  have hxpos : 0 < x.val := by
    by_contra hn
    have hx0 : x.val = 0 := by omega
    exact hx (hx0 ▸ dvd_zero L)
  have htop : 2 ≤ q * L := by nlinarith
  letI : Fact (1 < q * L) := ⟨by omega⟩
  have honeval : (1 : ZMod (q * L)).val = 1 := ZMod.val_one (q * L)
  have hprev : (x - 1).val = x.val - 1 := by
    simpa [honeval] using (ZMod.val_sub (a := x) (b := (1 : ZMod (q * L)))
      (by rw [honeval]; omega))
  unfold signedBoundary blockLiftWeight
  rw [hprev, pred_div_eq_div_of_not_dvd hL hxpos hx]
  simp

/-- Every nonzero block-lift boundary point is a dilated lower-level endpoint. -/
theorem blockLiftBoundary_supported_on_dilated_points
    {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 2 ≤ q) (hL : 0 < L) (h : ZMod q → ℂ)
    (x : ZMod (q * L))
    (hx : signedBoundary (blockLiftWeight h) x ≠ 0) :
    L ∣ x.val := by
  by_contra hnot
  exact hx (blockLiftBoundary_zero_off_dilated_support hq hL h x hnot)

/-- If a prime divides the block length, every surviving boundary point is a nonunit. -/
theorem blockLiftBoundary_nonunit_of_prime_dilation
    {p q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hp : p.Prime) (hq : 2 ≤ q) (hL : 0 < L) (hpL : p ∣ L)
    (h : ZMod q → ℂ) (x : ZMod (q * L))
    (hx : signedBoundary (blockLiftWeight h) x ≠ 0)
    (hpTop : p ∣ q * L) :
    ¬IsUnit x := by
  have hLx : L ∣ x.val :=
    blockLiftBoundary_supported_on_dilated_points hq hL h x hx
  have hpx : p ∣ x.val := dvd_trans hpL hLx
  intro hunit
  have hunitcast : IsUnit (x.val : ZMod (q * L)) := by
    simpa only [ZMod.natCast_zmod_val] using hunit
  have hcop : x.val.Coprime (q * L) :=
    (ZMod.isUnit_iff_coprime x.val (q * L)).mp hunitcast
  have hcop' : x.val.Coprime p := hcop.of_dvd_right hpTop
  exact (hp.coprime_iff_not_dvd.mp hcop'.symm) hpx

/-- Title: `Primitive invisibility of a lifted boundary`.

Primitive characters at the lifted level cannot see a support native to the lower level. -/
theorem primitiveTransform_blockLift_zero
    {p q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hp : p.Prime) (hq : 2 ≤ q) (hL : 0 < L) (hpL : p ∣ L)
    (h : ZMod q → ℂ) {χ : Character (q * L)} (hχ : χ.IsPrimitive) :
    carryTransform (blockLiftWeight h) χ = 0 := by
  apply no_unit_boundary_primitive_transform (by nlinarith) _ _ hχ
  intro u
  by_contra hne
  have hpTop : p ∣ q * L := dvd_mul_of_dvd_right hpL q
  exact blockLiftBoundary_nonunit_of_prime_dilation hp hq hL hpL h u.val hne hpTop
    u.isUnit

end NField.Alignment.LiftedBoundaryInvisibility
