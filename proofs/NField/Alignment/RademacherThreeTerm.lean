/-
Author: Alexander S. Petty
-/

import NField.Alignment.ThreeModulusFloorPartition

/-!
# Three-modulus Dedekind reciprocity

This module states the three-modulus terms in the same unit-ratio language as
the collision kernel.  The modulus-one boundary is proved directly from the
two-term reciprocity theorem developed in `DedekindReciprocity`.
-/

namespace NField.Alignment.RademacherThreeTerm

open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindReciprocity
open NField.Alignment.ThreeModulusFloorPartition
open NField.Alignment.CarryBoundarySpectra

/-- The symmetric two-coefficient Dedekind sum in exact rational arithmetic. -/
def arithmeticCoefficientDedekindTerm (x y m : ℕ) : ℚ :=
  ∑ t ∈ Finset.range m,
    rationalSawtooth (x * t) m * rationalSawtooth (y * t) m

/-- The symmetric two-coefficient Dedekind term at modulus `m`.  Written as a
unit ratio, this is the finite sum whose two sawtooth arguments have the
displayed coefficients. -/
noncomputable def coefficientDedekindTerm
    {m : ℕ} [NeZero m] (x y : ℕ)
    (_hxm : x.Coprime m) (_hym : y.Coprime m) : ℂ :=
  ((arithmeticCoefficientDedekindTerm x y m : ℚ) : ℂ)

/-- Multiplying one argument by a coprime coefficient is just the usual
unit-ratio Dedekind sum after finite reindexing. -/
theorem arithmeticCoefficientDedekindTerm_eq_ratio
    {m x y : ℕ} [NeZero m]
    (hxm : x.Coprime m) (hym : y.Coprime m) :
    coefficientDedekindTerm x y hxm hym =
      dedekindSum ((ZMod.unitOfCoprime x hxm)⁻¹ *
        ZMod.unitOfCoprime y hym) := by
  let ux := ZMod.unitOfCoprime x hxm
  let uy := ZMod.unitOfCoprime y hym
  rw [show coefficientDedekindTerm x y hxm hym =
      ∑ z : ZMod m,
        centeredSawtooth (ux.val * z) * centeredSawtooth (uy.val * z) by
    unfold coefficientDedekindTerm arithmeticCoefficientDedekindTerm
    rw [← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => rationalSawtooth (x * t) m *
        rationalSawtooth (y * t) m) m]
    rw [← (ZMod.finEquiv m).toEquiv.sum_comp]
    push_cast
    apply Finset.sum_congr rfl
    intro t _ht
    rw [show ((ZMod.finEquiv m).toEquiv t : ZMod m) =
        (t.val : ZMod m) by
      simpa using NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast t]
    have hxval : (ux.val * (t.val : ZMod m)).val = (x * t.val) % m := by
      simp [ux, ZMod.val_mul, ZMod.coe_unitOfCoprime, Nat.mul_mod]
    have hyval : (uy.val * (t.val : ZMod m)).val = (y * t.val) % m := by
      simp [uy, ZMod.val_mul, ZMod.coe_unitOfCoprime, Nat.mul_mod]
    rw [← rationalSawtooth_val_eq_centeredSawtooth
          (ux.val * (t.val : ZMod m)),
      ← rationalSawtooth_val_eq_centeredSawtooth
          (uy.val * (t.val : ZMod m)), hxval, hyval]
    unfold rationalSawtooth
    rw [Nat.mod_mod, Nat.mod_mod]]
  unfold dedekindSum
  let e : ZMod m ≃ ZMod m := ux⁻¹.mulLeft
  have hreindex := e.sum_comp (fun z : ZMod m =>
    centeredSawtooth (ux.val * z) * centeredSawtooth (uy.val * z))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro z _hz
  dsimp [e]
  change centeredSawtooth (ux.val * (ux⁻¹.val * z)) *
      centeredSawtooth (uy.val * (ux⁻¹.val * z)) =
    centeredSawtooth z * centeredSawtooth ((ux⁻¹ * uy).val * z)
  have hleft : ux.val * (ux⁻¹.val * z) = z := by
    rw [← mul_assoc, ← Units.val_mul]
    simp
  have hright : uy.val * (ux⁻¹.val * z) =
      ((ux⁻¹ * uy).val * z) := by
    change uy.val * (ux⁻¹.val * z) =
      (ux⁻¹.val * uy.val) * z
    ring
  rw [hleft, hright]

/-- The product of two quotient sequences on the positive interior. -/
def floorProductSum (m x y : ℕ) : ℕ :=
  ∑ t ∈ positiveInterior m, (x * t / m) * (y * t / m)

/-- On a nonzero interior residue, the periodic sawtooth is its linear term
minus the exact floor quotient. -/
theorem rationalSawtooth_mul_eq_linear_sub_floor
    {m h t : ℕ} (hm : 0 < m) (hhm : h.Coprime m)
    (ht : t ∈ positiveInterior m) :
    rationalSawtooth (h * t) m =
      (h : ℚ) * (t : ℚ) / (m : ℚ) -
        (((h * t) / m : ℕ) : ℚ) - 1 / 2 := by
  have ht' := mem_positiveInterior_iff.mp ht
  rw [rationalSawtooth_mul_of_coprime hhm ht'.1 ht'.2]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdiv := Nat.mod_add_div (h * t) m
  have hdivQ := congrArg (fun n : ℕ => (n : ℚ)) hdiv
  push_cast at hdivQ
  field_simp [hmQ]
  linarith [hdivQ]

/-- Exact floor expansion of a symmetric two-coefficient Dedekind term. -/
theorem arithmeticCoefficientDedekindTerm_expansion
    {m x y : ℕ} (hm : 0 < m)
    (hxm : x.Coprime m) (hym : y.Coprime m) :
    arithmeticCoefficientDedekindTerm x y m =
      ((x : ℚ) * (y : ℚ) / (m : ℚ) ^ 2) *
          (∑ t ∈ positiveInterior m, (t : ℚ) ^ 2) -
        ((x : ℚ) / (m : ℚ)) *
          (∑ t ∈ positiveInterior m,
            (t : ℚ) * (((y * t) / m : ℕ) : ℚ)) -
        ((y : ℚ) / (m : ℚ)) *
          (∑ t ∈ positiveInterior m,
            (t : ℚ) * (((x * t) / m : ℕ) : ℚ)) +
        (floorProductSum m x y : ℚ) -
        (((x : ℚ) + (y : ℚ)) / (2 * (m : ℚ))) *
          (∑ t ∈ positiveInterior m, (t : ℚ)) +
        (1 / 2) *
          ((∑ t ∈ positiveInterior m,
              (((x * t) / m : ℕ) : ℚ)) +
            ∑ t ∈ positiveInterior m,
              (((y * t) / m : ℕ) : ℚ)) +
        ((m - 1 : ℕ) : ℚ) / 4 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold arithmeticCoefficientDedekindTerm
  rw [sum_range_eq_sum_Ico_one
    (fun t => rationalSawtooth (x * t) m * rationalSawtooth (y * t) m)
    hm (by simp [rationalSawtooth_zero])]
  change (∑ t ∈ positiveInterior m,
      rationalSawtooth (x * t) m * rationalSawtooth (y * t) m) = _
  have hpoint (t : ℕ) (ht : t ∈ positiveInterior m) :
      rationalSawtooth (x * t) m * rationalSawtooth (y * t) m =
        ((x : ℚ) * (y : ℚ) / (m : ℚ) ^ 2) * (t : ℚ) ^ 2 -
          ((x : ℚ) / (m : ℚ)) *
            ((t : ℚ) * (((y * t) / m : ℕ) : ℚ)) -
          ((y : ℚ) / (m : ℚ)) *
            ((t : ℚ) * (((x * t) / m : ℕ) : ℚ)) +
          ((((x * t) / m : ℕ) : ℚ) *
            (((y * t) / m : ℕ) : ℚ)) -
          (((x : ℚ) + (y : ℚ)) / (2 * (m : ℚ))) * (t : ℚ) +
          (1 / 2) *
            (((((x * t) / m : ℕ) : ℚ)) +
              (((y * t) / m : ℕ) : ℚ)) + 1 / 4 := by
    rw [rationalSawtooth_mul_eq_linear_sub_floor hm hxm ht,
      rationalSawtooth_mul_eq_linear_sub_floor hm hym ht]
    field_simp [hmQ]
    ring
  rw [Finset.sum_congr rfl hpoint]
  unfold floorProductSum
  push_cast
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (positiveInterior m).card = m - 1 := by
    simp [positiveInterior]
  rw [hcard]
  have hWx :
      (∑ t ∈ positiveInterior m,
          (x : ℚ) * (m : ℚ)⁻¹ * (t : ℚ) *
            (((y * t) / m : ℕ) : ℚ)) =
        (x : ℚ) * (m : ℚ)⁻¹ *
          ∑ t ∈ positiveInterior m,
            (t : ℚ) * (((y * t) / m : ℕ) : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  have hWy :
      (∑ t ∈ positiveInterior m,
          (y : ℚ) * (m : ℚ)⁻¹ * (t : ℚ) *
            (((t * x) / m : ℕ) : ℚ)) =
        (y : ℚ) * (m : ℚ)⁻¹ *
          ∑ t ∈ positiveInterior m,
            (t : ℚ) * (((x * t) / m : ℕ) : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    simp only [Nat.mul_comm t x]
    ring
  have hP :
      (∑ t ∈ positiveInterior m,
          (((y * t) / m : ℕ) : ℚ) * (((t * x) / m : ℕ) : ℚ)) =
        ∑ t ∈ positiveInterior m,
          (((x * t) / m : ℕ) : ℚ) * (((y * t) / m : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro t _ht
    simp only [Nat.mul_comm t x]
    ring
  ring_nf
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hWx, hWy, hP]
  ring

theorem sum_positiveInterior_id {m : ℕ} (hm : 0 < m) :
    (∑ t ∈ positiveInterior m, (t : ℚ)) =
      (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  rw [show (∑ t ∈ positiveInterior m, (t : ℚ)) =
      ∑ t ∈ Finset.range m, (t : ℚ) by
    symm
    exact sum_range_eq_sum_Ico_one (fun t => (t : ℚ)) hm (by simp)]
  exact rational_sum_range_id m

theorem sum_positiveInterior_sq {m : ℕ} (hm : 0 < m) :
    (∑ t ∈ positiveInterior m, (t : ℚ) ^ 2) =
      (m : ℚ) * ((m : ℚ) - 1) * (2 * (m : ℚ) - 1) / 6 := by
  rw [show (∑ t ∈ positiveInterior m, (t : ℚ) ^ 2) =
      ∑ t ∈ Finset.range m, (t : ℚ) ^ 2 by
    symm
    exact sum_range_eq_sum_Ico_one (fun t => (t : ℚ) ^ 2) hm (by simp)]
  exact rational_sum_range_sq m

theorem sum_positiveInterior_floor
    {m h : ℕ} (hm : 0 < m) :
    (∑ t ∈ positiveInterior m, (((h * t) / m : ℕ) : ℚ)) =
      (floorSum m h : ℚ) := by
  unfold floorSum
  rw [sum_range_eq_sum_Ico_one (fun t => (h * t) / m) hm (by simp)]
  push_cast
  rfl

theorem sum_positiveInterior_weightedFloor
    {m h : ℕ} (hm : 0 < m) :
    (∑ t ∈ positiveInterior m,
        (t : ℚ) * (((h * t) / m : ℕ) : ℚ)) =
      (weightedFloorSum m h : ℚ) := by
  unfold weightedFloorSum
  rw [sum_range_eq_sum_Ico_one (fun t => t * ((h * t) / m)) hm (by simp)]
  push_cast
  rfl

/-- Closed floor form of the coefficient term.  All linear floor sums have
cancelled, leaving only the two weighted quotients and the floor product. -/
theorem arithmeticCoefficientDedekindTerm_closed
    {m x y : ℕ} (hm : 0 < m) (hx : 0 < x) (hy : 0 < y)
    (hxm : x.Coprime m) (hym : y.Coprime m) :
    arithmeticCoefficientDedekindTerm x y m =
      (x : ℚ) * (y : ℚ) * ((m : ℚ) - 1) *
          (2 * (m : ℚ) - 1) / (6 * (m : ℚ)) -
        (x : ℚ) * (weightedFloorSum m y : ℚ) / (m : ℚ) -
        (y : ℚ) * (weightedFloorSum m x : ℚ) / (m : ℚ) +
        (floorProductSum m x y : ℚ) - ((m : ℚ) - 1) / 4 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmOne : 1 ≤ m := by omega
  have hxOne : 1 ≤ x := by omega
  have hyOne : 1 ≤ y := by omega
  have hFxNat := floorSum_eq hm hxm
  have hFyNat := floorSum_eq hm hym
  have hFx := congrArg (fun n : ℕ => (n : ℚ)) hFxNat
  have hFy := congrArg (fun n : ℕ => (n : ℚ)) hFyNat
  push_cast [Nat.cast_sub hmOne, Nat.cast_sub hxOne] at hFx
  push_cast [Nat.cast_sub hmOne, Nat.cast_sub hyOne] at hFy
  rw [arithmeticCoefficientDedekindTerm_expansion hm hxm hym,
    sum_positiveInterior_sq hm,
    sum_positiveInterior_weightedFloor hm,
    sum_positiveInterior_weightedFloor hm,
    sum_positiveInterior_id hm,
    sum_positiveInterior_floor hm,
    sum_positiveInterior_floor hm]
  rw [show (floorSum m x : ℚ) =
      ((m : ℚ) - 1) * ((x : ℚ) - 1) / 2 by linarith [hFx],
    show (floorSum m y : ℚ) =
      ((m : ℚ) - 1) * ((y : ℚ) - 1) / 2 by linarith [hFy]]
  rw [Nat.cast_sub hmOne]
  field_simp [hmQ]
  ring

/-- Weighted floor sums for a transposed coprime pair.  This is the exact
form needed when the three cyclic coefficient expansions are collected. -/
theorem weightedFloorPair_div
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) (hhm : h.Coprime m) :
    (weightedFloorSum m h : ℚ) / (m : ℚ) +
        (weightedFloorSum h m : ℚ) / (h : ℚ) =
      2 * (m : ℚ) * (h : ℚ) / 3 -
        3 * ((m : ℚ) + (h : ℚ)) / 4 + 3 / 4 +
        ((m : ℚ) / (h : ℚ) + (h : ℚ) / (m : ℚ) -
          1 / ((m : ℚ) * (h : ℚ))) / 12 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hrecip := arithmeticDedekindSum_reciprocity hm hh hhm
  rw [arithmeticDedekindSum_eq_weightedFloorSum hm hhm,
    arithmeticDedekindSum_eq_weightedFloorSum hh hhm.symm] at hrecip
  field_simp [hmQ, hhQ] at hrecip ⊢
  linear_combination (-1 / 2 : ℚ) * hrecip

/-- Rademacher's three-term reciprocity in symmetric coefficient form, proved
from the finite largest-coordinate partition. -/
theorem arithmeticCoefficientDedekindTerm_threeTerm
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    arithmeticCoefficientDedekindTerm b c a +
        arithmeticCoefficientDedekindTerm c a b +
        arithmeticCoefficientDedekindTerm a b c =
      -1 / 4 + (1 / 12) *
        ((a : ℚ) / ((b : ℚ) * (c : ℚ)) +
          (b : ℚ) / ((c : ℚ) * (a : ℚ)) +
          (c : ℚ) / ((a : ℚ) * (b : ℚ))) := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hAB := weightedFloorPair_div ha hb hab.symm
  have hAC := weightedFloorPair_div ha hc hac.symm
  have hBC := weightedFloorPair_div hb hc hbc.symm
  have hPnat := threeModulus_floorProduct_sum ha hb hc hab hac hbc
  change floorProductSum a b c + floorProductSum b a c +
      floorProductSum c a b = (a - 1) * (b - 1) * (c - 1) at hPnat
  have hPswap : floorProductSum b a c = floorProductSum b c a := by
    unfold floorProductSum
    apply Finset.sum_congr rfl
    intro t _ht
    simp [Nat.mul_comm]
  rw [hPswap] at hPnat
  have hP := congrArg (fun n : ℕ => (n : ℚ)) hPnat
  push_cast at hP
  rw [arithmeticCoefficientDedekindTerm_closed ha hb hc hab.symm hac.symm,
    arithmeticCoefficientDedekindTerm_closed hb hc ha hbc.symm hab,
    arithmeticCoefficientDedekindTerm_closed hc ha hb hac hbc]
  calc
    _ =
        ((b : ℚ) * (c : ℚ) * ((a : ℚ) - 1) *
              (2 * (a : ℚ) - 1) / (6 * (a : ℚ)) +
          (c : ℚ) * (a : ℚ) * ((b : ℚ) - 1) *
              (2 * (b : ℚ) - 1) / (6 * (b : ℚ)) +
          (a : ℚ) * (b : ℚ) * ((c : ℚ) - 1) *
              (2 * (c : ℚ) - 1) / (6 * (c : ℚ))) +
        ((floorProductSum a b c : ℚ) +
          (floorProductSum b c a : ℚ) +
          (floorProductSum c a b : ℚ)) -
        (((a : ℚ) - 1) + ((b : ℚ) - 1) + ((c : ℚ) - 1)) / 4 -
        (c : ℚ) *
          ((weightedFloorSum a b : ℚ) / (a : ℚ) +
            (weightedFloorSum b a : ℚ) / (b : ℚ)) -
        (b : ℚ) *
          ((weightedFloorSum a c : ℚ) / (a : ℚ) +
            (weightedFloorSum c a : ℚ) / (c : ℚ)) -
        (a : ℚ) *
          ((weightedFloorSum b c : ℚ) / (b : ℚ) +
            (weightedFloorSum c b : ℚ) / (c : ℚ)) := by ring
    _ = _ := by
      rw [hAB, hAC, hBC, hP]
      rw [Nat.cast_sub (by omega : 1 ≤ a),
        Nat.cast_sub (by omega : 1 ≤ b),
        Nat.cast_sub (by omega : 1 ≤ c)]
      field_simp [haQ, hbQ, hcQ]
      ring

/-- Rademacher's three-term reciprocity for the complex collision-kernel
coefficient terms.  This is only scalar extension of the exact rational
identity above. -/
theorem coefficientDedekindTerm_threeTerm
    {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    coefficientDedekindTerm b c hab.symm hac.symm +
        coefficientDedekindTerm c a hbc.symm hab +
        coefficientDedekindTerm a b hac hbc =
      ((-1 / 4 + (1 / 12) *
        ((a : ℚ) / ((b : ℚ) * (c : ℚ)) +
          (b : ℚ) / ((c : ℚ) * (a : ℚ)) +
          (c : ℚ) / ((a : ℚ) * (b : ℚ))) : ℚ) : ℂ) := by
  unfold coefficientDedekindTerm
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℂ))
    (arithmeticCoefficientDedekindTerm_threeTerm ha hb hc hab hac hbc)
  push_cast at h
  simpa using h

theorem unitOfCoprime_one_eq_one
    (m : ℕ) [NeZero m] :
    ZMod.unitOfCoprime 1 (Nat.coprime_one_left m) = (1 : (ZMod m)ˣ) := by
  apply Units.val_injective
  rw [ZMod.coe_unitOfCoprime]
  simp

theorem coefficientDedekindTerm_self_left
    {m y : ℕ} [NeZero m] (hym : y.Coprime m) :
    coefficientDedekindTerm 1 y (Nat.coprime_one_left m) hym =
      dedekindSum (ZMod.unitOfCoprime y hym) := by
  rw [arithmeticCoefficientDedekindTerm_eq_ratio]
  rw [unitOfCoprime_one_eq_one]
  simp

theorem coefficientDedekindTerm_self_right
    {m x : ℕ} [NeZero m] (hxm : x.Coprime m) :
    coefficientDedekindTerm x 1 hxm (Nat.coprime_one_left m) =
      dedekindSum (ZMod.unitOfCoprime x hxm) := by
  rw [arithmeticCoefficientDedekindTerm_eq_ratio]
  rw [unitOfCoprime_one_eq_one, mul_one, dedekindSum_inv]

/-- The modulus-one edge of Rademacher's reduction.  This is ordinary
two-term reciprocity, with inversion invariance accounting for the inverse
coefficient used by the three-modulus notation. -/
theorem coefficientDedekindTerm_reciprocity_one
    {a m : ℕ} [NeZero a] [NeZero m]
    (ha : 0 < a) (hm : 0 < m) (ham : a.Coprime m) :
    coefficientDedekindTerm 1 a (Nat.coprime_one_left m) ham +
        coefficientDedekindTerm 1 m (Nat.coprime_one_left a) ham.symm =
      ((-1 / 4 : ℚ) +
        (1 / 12) *
          ((a : ℚ) / (m : ℚ) + (m : ℚ) / (a : ℚ) +
            1 / ((a : ℚ) * (m : ℚ))) : ℚ) := by
  rw [coefficientDedekindTerm_self_left,
    coefficientDedekindTerm_self_left,
    dedekindSum_unitOfCoprime_eq_arithmeticDedekindSum ham,
    dedekindSum_unitOfCoprime_eq_arithmeticDedekindSum ham.symm]
  rw [← Rat.cast_add]
  congr 1
  exact arithmeticDedekindSum_reciprocity hm ha ham

end NField.Alignment.RademacherThreeTerm
