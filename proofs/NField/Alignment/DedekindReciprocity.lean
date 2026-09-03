/-
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindCollisionKernel
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

/-!
# Dedekind reciprocity

This module develops the arithmetic form of the classical Dedekind sum from
the finite centered-sawtooth definition used by nfield.  All floor and residue
identities are kept over `ℚ`; the final bridge casts them to the complex-valued
collision kernel.
-/

namespace NField.Alignment.DedekindReciprocity

open scoped BigOperators ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.DedekindCollisionKernel

/-- The periodic first Bernoulli function in exact rational arithmetic. -/
def rationalSawtooth (x m : ℕ) : ℚ :=
  if x % m = 0 then 0 else ((x % m : ℕ) : ℚ) / (m : ℚ) - 1 / 2

/-- The classical Dedekind sum with a natural numerator and modulus. -/
def arithmeticDedekindSum (h m : ℕ) : ℚ :=
  ∑ x ∈ Finset.range m, rationalSawtooth x m * rationalSawtooth (h * x) m

/-- The weighted floor sum occurring in the elementary reciprocity proof. -/
def weightedFloorSum (m h : ℕ) : ℕ :=
  ∑ x ∈ Finset.range m, x * ((h * x) / m)

/-- The unweighted floor sum used by the reciprocity calculation. -/
def floorSum (m h : ℕ) : ℕ :=
  ∑ x ∈ Finset.range m, (h * x) / m

/-- The square moment of the same floor sequence. -/
def floorSquareSum (m h : ℕ) : ℕ :=
  ∑ x ∈ Finset.range m, ((h * x) / m) ^ 2

theorem rationalSawtooth_of_lt
    {x m : ℕ} (hx : 0 < x) (hxm : x < m) :
    rationalSawtooth x m = (x : ℚ) / (m : ℚ) - 1 / 2 := by
  unfold rationalSawtooth
  rw [Nat.mod_eq_of_lt hxm, if_neg hx.ne']

theorem rationalSawtooth_mul_of_coprime
    {h x m : ℕ} (hhm : h.Coprime m)
    (hx : 0 < x) (hxm : x < m) :
    rationalSawtooth (h * x) m =
      (((h * x) % m : ℕ) : ℚ) / (m : ℚ) - 1 / 2 := by
  unfold rationalSawtooth
  rw [if_neg]
  intro hz
  have hmdvd : m ∣ h * x := Nat.dvd_iff_mod_eq_zero.mpr hz
  have hmx : m ∣ x := hhm.symm.dvd_of_dvd_mul_left hmdvd
  have : m ≤ x := Nat.le_of_dvd hx hmx
  omega

theorem rationalSawtooth_zero (m : ℕ) : rationalSawtooth 0 m = 0 := by
  simp [rationalSawtooth]

/-- The rational and complex sawtooth normalizations agree on a residue
class. -/
theorem rationalSawtooth_val_eq_centeredSawtooth
    {m : ℕ} [NeZero m] (x : ZMod m) :
    ((rationalSawtooth x.val m : ℚ) : ℂ) = centeredSawtooth x := by
  unfold rationalSawtooth centeredSawtooth
  rw [Nat.mod_eq_of_lt x.val_lt]
  by_cases hx : x = 0
  · subst x
    simp
  · have hxval : x.val ≠ 0 := by
      intro hzero
      apply hx
      apply ZMod.val_injective m
      simpa using hzero
    rw [if_neg hxval, if_neg hx]
    push_cast
    rfl

/-- A coprime multiplier permutes the least residues. -/
noncomputable def coprimeResidueEquiv
    {m h : ℕ} [NeZero m] (hhm : h.Coprime m) : Fin m ≃ Fin m :=
  (ZMod.finEquiv m).toEquiv.trans <|
    (ZMod.unitOfCoprime h hhm).mulLeft.trans
      (ZMod.finEquiv m).toEquiv.symm

theorem coprimeResidueEquiv_val
    {m h : ℕ} [NeZero m] (hhm : h.Coprime m) (x : Fin m) :
    (coprimeResidueEquiv hhm x).val = (h * x.val) % m := by
  let e := coprimeResidueEquiv hhm
  have hz :
      (ZMod.finEquiv m) (e x) =
        (ZMod.unitOfCoprime h hhm).val * (ZMod.finEquiv m) x := by
    simp [e, coprimeResidueEquiv]
  have hv := congrArg ZMod.val hz
  rw [NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast,
    NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast,
    ZMod.val_natCast, Nat.mod_eq_of_lt (e x).isLt,
    ZMod.val_mul, ZMod.val_natCast,
    Nat.mod_eq_of_lt x.isLt] at hv
  change (coprimeResidueEquiv hhm x).val = _ at hv
  simpa [ZMod.coe_unitOfCoprime, Nat.mul_mod] using hv

theorem sum_coprime_mul_mod
    {m h : ℕ} (hm : 0 < m) (hhm : h.Coprime m) :
    ∑ x ∈ Finset.range m, (h * x) % m = m * (m - 1) / 2 := by
  letI : NeZero m := ⟨hm.ne'⟩
  let e := coprimeResidueEquiv hhm
  calc
    (∑ x ∈ Finset.range m, (h * x) % m) =
        ∑ x : Fin m, (h * x.val) % m := by
          rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => (h * x) % m) m]
    _ = ∑ x : Fin m, (e x).val := by
          apply Finset.sum_congr rfl
          intro x _
          exact (coprimeResidueEquiv_val hhm x).symm
    _ = ∑ x : Fin m, x.val := e.sum_comp (fun x : Fin m => x.val)
    _ = ∑ x ∈ Finset.range m, x := by
          rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => x) m]
    _ = m * (m - 1) / 2 := Finset.sum_range_id m

theorem sum_coprime_mul_mod_sq
    {m h : ℕ} (hm : 0 < m) (hhm : h.Coprime m) :
    ∑ x ∈ Finset.range m, ((h * x) % m) ^ 2 =
      ∑ x ∈ Finset.range m, x ^ 2 := by
  letI : NeZero m := ⟨hm.ne'⟩
  let e := coprimeResidueEquiv hhm
  calc
    (∑ x ∈ Finset.range m, ((h * x) % m) ^ 2) =
        ∑ x : Fin m, ((h * x.val) % m) ^ 2 := by
          rw [Fin.sum_univ_eq_sum_range
            (fun x : ℕ => ((h * x) % m) ^ 2) m]
    _ = ∑ x : Fin m, (e x).val ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [coprimeResidueEquiv_val hhm]
    _ = ∑ x : Fin m, x.val ^ 2 := e.sum_comp (fun x : Fin m => x.val ^ 2)
    _ = ∑ x ∈ Finset.range m, x ^ 2 := by
          rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => x ^ 2) m]

/-- The complex collision-kernel Dedekind sum is the scalar extension of the
exact rational arithmetic sum. -/
theorem dedekindSum_unitOfCoprime_eq_arithmeticDedekindSum
    {m h : ℕ} [NeZero m] (hhm : h.Coprime m) :
    dedekindSum (ZMod.unitOfCoprime h hhm) =
      ((arithmeticDedekindSum h m : ℚ) : ℂ) := by
  unfold dedekindSum arithmeticDedekindSum
  calc
    (∑ x : ZMod m,
        centeredSawtooth x *
          centeredSawtooth ((ZMod.unitOfCoprime h hhm).val * x)) =
        ∑ x : ZMod m,
          ((rationalSawtooth x.val m : ℚ) : ℂ) *
            ((rationalSawtooth
              (((ZMod.unitOfCoprime h hhm).val * x).val) m : ℚ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [rationalSawtooth_val_eq_centeredSawtooth,
            rationalSawtooth_val_eq_centeredSawtooth]
    _ = ∑ x : ZMod m,
          ((rationalSawtooth x.val m *
            rationalSawtooth (((h * x.val) % m)) m : ℚ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro x _
          have hval :
              (((ZMod.unitOfCoprime h hhm).val * x).val) =
                (h * x.val) % m := by
            rw [ZMod.val_mul, ZMod.coe_unitOfCoprime,
              ZMod.val_natCast]
            simp [Nat.mul_mod]
          rw [hval]
          push_cast
          rfl
    _ = ((∑ x : ZMod m,
          rationalSawtooth x.val m *
            rationalSawtooth ((h * x.val) % m) m : ℚ) : ℂ) := by
          push_cast
          rfl
    _ = ((∑ x : Fin m,
          rationalSawtooth x.val m *
            rationalSawtooth ((h * x.val) % m) m : ℚ) : ℂ) := by
          congr 1
          calc
            (∑ x : ZMod m,
                rationalSawtooth x.val m *
                  rationalSawtooth (h * x.val % m) m) =
                ∑ x : Fin m,
                  rationalSawtooth (((ZMod.finEquiv m).toEquiv x).val) m *
                    rationalSawtooth
                      (h * ((ZMod.finEquiv m).toEquiv x).val % m) m :=
                ((ZMod.finEquiv m).toEquiv.sum_comp (fun x : ZMod m =>
                  rationalSawtooth x.val m *
                    rationalSawtooth (h * x.val % m) m)).symm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x _
              have hval : ((ZMod.finEquiv m).toEquiv x).val = x.val := by
                have heq : ((ZMod.finEquiv m).toEquiv x : ZMod m) =
                    (x.val : ZMod m) := by
                  simpa using
                    NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast x
                rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
              rw [hval]
    _ = ((∑ x ∈ Finset.range m,
          rationalSawtooth x m * rationalSawtooth (h * x) m : ℚ) : ℂ) := by
          congr 1
          rw [Fin.sum_univ_eq_sum_range
            (fun x : ℕ => rationalSawtooth x m *
              rationalSawtooth (h * x % m) m) m]
          apply Finset.sum_congr rfl
          intro x hx
          rw [show rationalSawtooth ((h * x) % m) m =
              rationalSawtooth (h * x) m by
            unfold rationalSawtooth
            rw [Nat.mod_mod]]

/-- Exact sum of the quotient sequence produced by a coprime residue
permutation. -/
theorem floorSum_eq
    {m h : ℕ} (hm : 0 < m) (hhm : h.Coprime m) :
    2 * floorSum m h = (m - 1) * (h - 1) := by
  have hdecomp :
      m * floorSum m h +
          ∑ x ∈ Finset.range m, (h * x) % m =
        h * ∑ x ∈ Finset.range m, x := by
    unfold floorSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    simpa [Nat.mul_comm] using Nat.div_add_mod (h * x) m
  rw [sum_coprime_mul_mod hm hhm, Finset.sum_range_id] at hdecomp
  have hmEven := (Nat.even_mul_pred_self m).two_dvd
  have htri : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.mul_div_cancel' hmEven
  by_cases hh : h = 0
  · subst h
    have hmone : m = 1 := by simpa using hhm
    subst m
    simp [floorSum]
  · have hhform : h = (h - 1) + 1 := by omega
    have hdoubled :
        2 * m * floorSum m h + m * (m - 1) =
          h * (m * (m - 1)) := by
      calc
        2 * m * floorSum m h + m * (m - 1) =
            2 * (m * floorSum m h + m * (m - 1) / 2) := by
              rw [mul_add, htri]
              ring
        _ = 2 * (h * (m * (m - 1) / 2)) := by rw [hdecomp]
        _ = h * (m * (m - 1)) := by
          calc
            2 * (h * (m * (m - 1) / 2)) =
                h * (2 * (m * (m - 1) / 2)) := by ring
            _ = h * (m * (m - 1)) := by rw [htri]
    have hhmul :
        h * (m * (m - 1)) =
          (h - 1) * (m * (m - 1)) + m * (m - 1) := by
      conv_lhs => rw [hhform]
      ring
    rw [hhmul] at hdoubled
    have hcancel := Nat.add_right_cancel hdoubled
    have hmCancel :
        m * (2 * floorSum m h) = m * ((m - 1) * (h - 1)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcancel
    exact Nat.eq_of_mul_eq_mul_left hm hmCancel

theorem sum_range_eq_sum_Ico_one
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {m : ℕ} (hm : 0 < m) (hf0 : f 0 = 0) :
    ∑ x ∈ Finset.range m, f x = ∑ x ∈ Finset.Ico 1 m, f x := by
  have hrange : Finset.range m = insert 0 (Finset.Ico 1 m) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert (by simp), hf0, zero_add]

theorem rational_sum_range_id_early (m : ℕ) :
    ∑ x ∈ Finset.range m, (x : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Squaring the residue decomposition gives the exact quadratic floor
identity used in Dedekind reciprocity. -/
theorem residueSquare_floor_identity
    {m h : ℕ} (hm : 0 < m) (hhm : h.Coprime m) :
    2 * h * m * weightedFloorSum m h =
      (h ^ 2 - 1) * (∑ x ∈ Finset.range m, x ^ 2) +
        m ^ 2 * floorSquareSum m h := by
  have hpoint (x : ℕ) :
      ((h * x) % m) ^ 2 + 2 * h * m * (x * ((h * x) / m)) =
        h ^ 2 * x ^ 2 + m ^ 2 * ((h * x) / m) ^ 2 := by
    have hdiv := Nat.mod_add_div (h * x) m
    calc
      ((h * x) % m) ^ 2 + 2 * h * m * (x * ((h * x) / m)) =
          ((h * x) % m) ^ 2 +
            2 * (h * x) * m * ((h * x) / m) := by ring
      _ = ((h * x) % m) ^ 2 +
            2 * (((h * x) % m) + m * ((h * x) / m)) * m *
              ((h * x) / m) := by rw [hdiv]
      _ = (((h * x) % m) + m * ((h * x) / m)) ^ 2 +
            m ^ 2 * ((h * x) / m) ^ 2 := by ring
      _ = h ^ 2 * x ^ 2 + m ^ 2 * ((h * x) / m) ^ 2 := by
        rw [hdiv]
        ring
  have hsum := Finset.sum_congr rfl
    (fun x (_hx : x ∈ Finset.range m) => hpoint x)
  rw [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [sum_coprime_mul_mod_sq hm hhm] at hsum
  unfold weightedFloorSum floorSquareSum
  by_cases hh : h = 0
  · subst h
    have hmone : m = 1 := by simpa using hhm
    subst m
    simp
  · have hhsq : h ^ 2 = (h ^ 2 - 1) + 1 := by
      have : 0 < h ^ 2 := pow_pos (Nat.pos_of_ne_zero hh) 2
      omega
    rw [hhsq] at hsum
    nlinarith

/-- A weighted floor sum is the weighted lattice-point count below its
coprime diagonal. -/
theorem weightedFloorSum_eq_latticeSum
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) :
    (weightedFloorSum h m : ℚ) =
      ∑ x ∈ Finset.Ico 1 m, ∑ y ∈ Finset.Ico 1 h,
        if x * h ≤ m * y then (y : ℚ) else 0 := by
  rw [show (weightedFloorSum h m : ℚ) =
      ∑ y ∈ Finset.Ico 1 h, ((y * ((m * y) / h) : ℕ) : ℚ) by
    unfold weightedFloorSum
    rw [sum_range_eq_sum_Ico_one (fun y => y * ((m * y) / h)) hh]
    · push_cast
      rfl
    · simp]
  calc
    (∑ y ∈ Finset.Ico 1 h, ((y * ((m * y) / h) : ℕ) : ℚ)) =
        ∑ y ∈ Finset.Ico 1 h, ∑ x ∈ Finset.Ico 1 m,
          if x * h ≤ m * y then (y : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      have hylt : y < h := (Finset.mem_Ico.mp hy).2
      have hbound : m * y / h ≤ m - 1 := by
        have hlt : m * y / h < m := by
          rw [Nat.div_lt_iff_lt_mul hh]
          exact Nat.mul_lt_mul_of_pos_left hylt hm
        omega
      have hcard := ZMod.div_eq_filter_card hh hbound
      have hmpred : (m - 1).succ = m := by omega
      rw [hmpred] at hcard
      calc
        ((y * ((m * y) / h) : ℕ) : ℚ) =
            (y : ℚ) *
              ((Finset.Ico 1 m).filter (fun x => x * h ≤ m * y)).card := by
                rw [hcard]
                push_cast
                rfl
        _ = _ := by
          calc
            (y : ℚ) *
                ((Finset.Ico 1 m).filter
                  (fun x => x * h ≤ m * y)).card =
                ∑ _x ∈ (Finset.Ico 1 m).filter
                  (fun x => x * h ≤ m * y), (y : ℚ) := by
                    simp [mul_comm]
            _ = _ := by rw [Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]

/-- Exact complementary-triangle formula for the transposed weighted floor
sum. -/
theorem weightedFloorSum_transpose
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) (hhm : h.Coprime m) :
    2 * (weightedFloorSum h m : ℚ) =
      ((m : ℚ) - 1) * (h : ℚ) * ((h : ℚ) - 1) -
        (floorSquareSum m h : ℚ) - (floorSum m h : ℚ) := by
  rw [weightedFloorSum_eq_latticeSum hm hh]
  have hinner (x : ℕ) (hx : x ∈ Finset.Ico 1 m) :
      (∑ y ∈ Finset.Ico 1 h,
          if x * h ≤ m * y then (y : ℚ) else 0) =
        (h : ℚ) * ((h : ℚ) - 1) / 2 -
          ((((h * x) / m : ℕ) : ℚ) *
            ((((h * x) / m : ℕ) : ℚ) + 1) / 2) := by
    have hxpos : 0 < x := (Finset.mem_Ico.mp hx).1
    have hxlt : x < m := (Finset.mem_Ico.mp hx).2
    have hTlt : (h * x) / m < h := by
      rw [Nat.div_lt_iff_lt_mul hm]
      exact Nat.mul_lt_mul_of_pos_left hxlt hh
    have hpred (y : ℕ) (hy : y ∈ Finset.Ico 1 h) :
        x * h ≤ m * y ↔ (h * x) / m < y := by
      have hypos : 0 < y := (Finset.mem_Ico.mp hy).1
      have hylt : y < h := (Finset.mem_Ico.mp hy).2
      have hne : x * h ≠ m * y := by
        intro heq
        have hmdvd : m ∣ h * x := by
          use y
          simpa [Nat.mul_comm] using heq
        have hmx : m ∣ x := hhm.symm.dvd_of_dvd_mul_left hmdvd
        exact (Nat.not_dvd_of_pos_of_lt hxpos hxlt) hmx
      constructor
      · intro hle
        have hlt : h * x < y * m := by
          have hstrict : x * h < m * y := lt_of_le_of_ne hle hne
          simpa [Nat.mul_comm] using hstrict
        exact (Nat.div_lt_iff_lt_mul hm).2 hlt
      · intro hlt
        have := (Nat.div_lt_iff_lt_mul hm).1 hlt
        simpa [Nat.mul_comm] using this.le
    calc
      _ = ∑ y ∈ Finset.Ico (((h * x) / m) + 1) h, (y : ℚ) := by
        rw [← Finset.sum_filter]
        congr 1
        ext y
        by_cases hy : y ∈ Finset.Ico 1 h
        · rw [Finset.mem_filter, and_iff_right hy, hpred y hy]
          rw [Finset.mem_Ico]
          constructor
          · intro hlt
            exact ⟨Nat.succ_le_iff.mpr hlt, (Finset.mem_Ico.mp hy).2⟩
          · intro htarget
            exact Nat.lt_iff_add_one_le.mpr htarget.1
        · have hnotTarget : y ∉ Finset.Ico (h * x / m + 1) h := by
            intro hyt
            have hyt' := Finset.mem_Ico.mp hyt
            apply hy
            have hTltY : (h * x) / m < y :=
              Nat.lt_of_succ_le hyt'.1
            have hypos : 0 < y :=
              lt_of_le_of_lt (Nat.zero_le ((h * x) / m)) hTltY
            exact Finset.mem_Ico.mpr ⟨hypos, hyt'.2⟩
          simp [hy, hnotTarget]
      _ = _ := by
        rw [Finset.sum_Ico_eq_sub (fun y : ℕ => (y : ℚ)) (by omega)]
        rw [rational_sum_range_id_early, rational_sum_range_id_early]
        push_cast
        ring
  have hreplace :
      (∑ x ∈ Finset.Ico 1 m, ∑ y ∈ Finset.Ico 1 h,
          if x * h ≤ m * y then (y : ℚ) else 0) =
        ∑ x ∈ Finset.Ico 1 m,
          ((h : ℚ) * ((h : ℚ) - 1) / 2 -
            ((((h * x) / m : ℕ) : ℚ) *
              ((((h * x) / m : ℕ) : ℚ) + 1) / 2)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hinner x hx
  rw [hreplace]
  rw [Finset.sum_sub_distrib]
  have hcard : (Finset.Ico 1 m).card = m - 1 := by simp
  rw [Finset.sum_const, hcard]
  have hfloorIco :
      (∑ x ∈ Finset.Ico 1 m, ((((h * x) / m : ℕ) : ℚ))) =
        (floorSum m h : ℚ) := by
    unfold floorSum
    rw [sum_range_eq_sum_Ico_one (fun x => (h * x) / m) hm]
    · push_cast
      rfl
    · simp
  have hsquareIco :
      (∑ x ∈ Finset.Ico 1 m,
          ((((h * x) / m : ℕ) : ℚ)) ^ 2) =
        (floorSquareSum m h : ℚ) := by
    unfold floorSquareSum
    rw [sum_range_eq_sum_Ico_one (fun x => ((h * x) / m) ^ 2) hm]
    · push_cast
      rfl
    · simp
  have hquadraticIco :
      (∑ x ∈ Finset.Ico 1 m,
          ((((h * x) / m : ℕ) : ℚ) *
            ((((h * x) / m : ℕ) : ℚ) + 1) / 2)) =
        ((floorSquareSum m h : ℚ) + (floorSum m h : ℚ)) / 2 := by
    calc
      _ = ∑ x ∈ Finset.Ico 1 m,
          (((((h * x) / m : ℕ) : ℚ) ^ 2 +
            (((h * x) / m : ℕ) : ℚ)) / 2) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = ((∑ x ∈ Finset.Ico 1 m,
              ((((h * x) / m : ℕ) : ℚ)) ^ 2) +
            (∑ x ∈ Finset.Ico 1 m,
              (((h * x) / m : ℕ) : ℚ))) / 2 := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      _ = _ := by rw [hsquareIco, hfloorIco]
  rw [hquadraticIco]
  simp only [nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  ring

theorem rational_sum_range_id (m : ℕ) :
    ∑ x ∈ Finset.range m, (x : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem rational_sum_range_sq (m : ℕ) :
    ∑ x ∈ Finset.range m, (x : ℚ) ^ 2 =
      (m : ℚ) * ((m : ℚ) - 1) * (2 * (m : ℚ) - 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact floor-sum expansion of a Dedekind sum. -/
theorem arithmeticDedekindSum_eq_weightedFloorSum
    {m h : ℕ} (hm : 0 < m) (hhm : h.Coprime m) :
    arithmeticDedekindSum h m =
      (h : ℚ) * ((m : ℚ) - 1) * (2 * (m : ℚ) - 1) /
          (6 * (m : ℚ)) -
        (weightedFloorSum m h : ℚ) / (m : ℚ) -
        ((m : ℚ) - 1) / 4 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.range m) :
      rationalSawtooth x m * rationalSawtooth (h * x) m =
        ((x : ℚ) / (m : ℚ) - 1 / 2) *
            ((((h * x) % m : ℕ) : ℚ) / (m : ℚ) - 1 / 2) -
          if x = 0 then 1 / 4 else 0 := by
    have hxm : x < m := Finset.mem_range.mp hxmem
    by_cases hx : x = 0
    · subst x
      simp [rationalSawtooth_zero]
      ring
    · rw [rationalSawtooth_of_lt (Nat.pos_of_ne_zero hx) hxm,
        rationalSawtooth_mul_of_coprime hhm (Nat.pos_of_ne_zero hx) hxm]
      simp [hx]
  unfold arithmeticDedekindSum
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hcorrection :
      (∑ x ∈ Finset.range m, if x = 0 then (1 / 4 : ℚ) else 0) = 1 / 4 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro x _ hx
      simp [hx]
    · simp [hm]
  rw [hcorrection]
  have hresidueSumQ :
      (∑ x ∈ Finset.range m, ((((h * x) % m : ℕ) : ℚ))) =
        (m : ℚ) * ((m : ℚ) - 1) / 2 := by
    rw [← Nat.cast_sum, sum_coprime_mul_mod hm hhm]
    rw [Nat.cast_div (Nat.even_mul_pred_self m).two_dvd (by norm_num : (2 : ℚ) ≠ 0)]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hproductSum :
      (∑ x ∈ Finset.range m,
        (x : ℚ) * ((((h * x) % m : ℕ) : ℚ))) =
        (h : ℚ) *
            (∑ x ∈ Finset.range m, (x : ℚ) ^ 2) -
          (m : ℚ) * (weightedFloorSum m h : ℚ) := by
    calc
      (∑ x ∈ Finset.range m,
          (x : ℚ) * ((((h * x) % m : ℕ) : ℚ))) =
        ∑ x ∈ Finset.range m,
          ((h : ℚ) * (x : ℚ) ^ 2 -
            (m : ℚ) * ((x * ((h * x) / m) : ℕ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro x _
          have hdiv := Nat.mod_add_div (h * x) m
          have hdivQ := congrArg (fun n : ℕ => (n : ℚ)) hdiv
          push_cast at hdivQ
          rw [Nat.cast_mul]
          linear_combination (x : ℚ) * hdivQ
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        unfold weightedFloorSum
        push_cast
        rfl
  have hexpandSum :
      (∑ x ∈ Finset.range m,
        ((x : ℚ) / (m : ℚ) - 1 / 2) *
          ((((h * x) % m : ℕ) : ℚ) / (m : ℚ) - 1 / 2)) =
        (m : ℚ)⁻¹ ^ 2 *
            (∑ x ∈ Finset.range m,
              (x : ℚ) * ((((h * x) % m : ℕ) : ℚ))) -
          (2 * (m : ℚ))⁻¹ *
            ((∑ x ∈ Finset.range m, (x : ℚ)) +
              ∑ x ∈ Finset.range m,
                ((((h * x) % m : ℕ) : ℚ))) +
          (m : ℚ) / 4 := by
    calc
      _ = ∑ x ∈ Finset.range m,
          ((m : ℚ)⁻¹ ^ 2 *
              ((x : ℚ) * ((((h * x) % m : ℕ) : ℚ))) -
            (2 * (m : ℚ))⁻¹ *
              ((x : ℚ) + ((((h * x) % m : ℕ) : ℚ))) + 1 / 4) := by
            apply Finset.sum_congr rfl
            intro x _
            field_simp [hmQ]
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
        simp
        ring
  calc
    (∑ x ∈ Finset.range m,
        ((x : ℚ) / (m : ℚ) - 1 / 2) *
            ((((h * x) % m : ℕ) : ℚ) / (m : ℚ) - 1 / 2)) - 1 / 4 =
      (m : ℚ)⁻¹ ^ 2 *
          (∑ x ∈ Finset.range m,
            (x : ℚ) * ((((h * x) % m : ℕ) : ℚ))) -
        (2 * (m : ℚ))⁻¹ *
          ((∑ x ∈ Finset.range m, (x : ℚ)) +
            ∑ x ∈ Finset.range m, ((((h * x) % m : ℕ) : ℚ))) +
        (m : ℚ) / 4 - 1 / 4 := by
          rw [hexpandSum]
    _ = _ := by
      rw [hproductSum, rational_sum_range_sq, rational_sum_range_id,
        hresidueSumQ]
      field_simp [hmQ]
      ring

/-- The classical two-term Dedekind reciprocity law, proved from the finite
floor and lattice identities above. -/
theorem arithmeticDedekindSum_reciprocity
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) (hhm : h.Coprime m) :
    arithmeticDedekindSum h m + arithmeticDedekindSum m h =
      -1 / 4 +
        (1 / 12) *
          ((h : ℚ) / (m : ℚ) + (m : ℚ) / (h : ℚ) +
            1 / ((h : ℚ) * (m : ℚ))) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hmOne : 1 ≤ m := by omega
  have hhOne : 1 ≤ h := by omega
  have hhSqOne : 1 ≤ h ^ 2 := by nlinarith
  have hResidueQ := congrArg (fun n : ℕ => (n : ℚ))
    (residueSquare_floor_identity hm hhm)
  push_cast [Nat.cast_sub hhSqOne] at hResidueQ
  rw [rational_sum_range_sq] at hResidueQ
  have hA :
      (weightedFloorSum m h : ℚ) =
        (((h : ℚ) ^ 2 - 1) *
              ((m : ℚ) * ((m : ℚ) - 1) *
                (2 * (m : ℚ) - 1) / 6) +
            (m : ℚ) ^ 2 * (floorSquareSum m h : ℚ)) /
          (2 * (h : ℚ) * (m : ℚ)) := by
    field_simp [hmQ, hhQ]
    have hscaled := congrArg
      (fun z : ℚ => (6 / (m : ℚ)) * z) hResidueQ
    field_simp [hmQ] at hscaled
    ring_nf at hscaled ⊢
    exact hscaled
  have hTranspose := weightedFloorSum_transpose hm hh hhm
  have hB :
      (weightedFloorSum h m : ℚ) =
        (((m : ℚ) - 1) * (h : ℚ) * ((h : ℚ) - 1) -
            (floorSquareSum m h : ℚ) - (floorSum m h : ℚ)) / 2 := by
    linarith
  have hFloorQ := congrArg (fun n : ℕ => (n : ℚ))
    (floorSum_eq hm hhm)
  push_cast [Nat.cast_sub hmOne, Nat.cast_sub hhOne] at hFloorQ
  have hF :
      (floorSum m h : ℚ) =
        ((m : ℚ) - 1) * ((h : ℚ) - 1) / 2 := by
    linarith
  rw [arithmeticDedekindSum_eq_weightedFloorSum hm hhm,
    arithmeticDedekindSum_eq_weightedFloorSum hh hhm.symm,
    hA, hB, hF]
  field_simp [hmQ, hhQ]
  ring

end NField.Alignment.DedekindReciprocity
