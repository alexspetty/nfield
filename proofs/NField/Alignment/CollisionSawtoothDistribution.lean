/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindCollisionKernel

/-!
# Endpoint-complete distribution of the midpoint sawtooth

The zero residue has value zero. All reduction fibers, including the zero
fiber and modulus one, satisfy the multiplication formula. Unit twisting
commutes with reduction, so these finite sums give the conditional rows
used by the profinite Dedekind pairing.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSawtoothDistribution

open scoped BigOperators ZMod
open CollisionCharacterStructure CarryBoundarySpectra ConductorDepthSawtooth
open DedekindCollisionKernel

theorem sawtooth_fin_fiber {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 0 < q) (hL : 0 < L) (A : Fin q) :
    (∑ j : Fin L,
      centeredSawtooth ((A.val + q * j.val : ℕ) : ZMod (q * L))) =
      centeredSawtooth (A.val : ZMod q) := by
  classical
  letI : NeZero L := ⟨hL.ne'⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpoint (j : Fin L) : A.val + q * j.val < q * L := by
    have hAq := A.isLt
    have hj := j.isLt
    nlinarith
  have hzero (j : Fin L) :
      ((A.val + q * j.val : ℕ) : ZMod (q * L)) = 0 ↔
        A.val = 0 ∧ j.val = 0 := by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
      Nat.mod_eq_of_lt (hpoint j)]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨ha, hj⟩
      simp [ha, hj]
  have hterm (j : Fin L) :
      centeredSawtooth ((A.val + q * j.val : ℕ) : ZMod (q * L)) =
        ((A.val : ℂ) + (q : ℂ) * j.val) / ((q : ℂ) * L) - 1/2 +
          if A.val = 0 ∧ j.val = 0 then 1/2 else 0 := by
    unfold centeredSawtooth
    rw [if_congr (hzero j) rfl rfl, ZMod.val_natCast,
      Nat.mod_eq_of_lt (hpoint j)]
    push_cast
    split_ifs with hz
    · simp [hz.1, hz.2]
    · ring
  have hsumj : (∑ j : Fin L, (j.val : ℂ)) =
      (L : ℂ) * ((L : ℂ) - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact complex_sum_range_id L
  have hcorrection :
      (∑ j : Fin L, if A.val = 0 ∧ j.val = 0 then (1/2 : ℂ) else 0) =
        if A.val = 0 then 1/2 else 0 := by
    by_cases ha : A.val = 0
    · simp [ha, show ∀ j : Fin L, j.val = 0 ↔ j = 0 from
        fun j => ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩]
    · simp [ha]
  have hbase : centeredSawtooth (A.val : ZMod q) =
      (A.val : ℂ) / q - 1/2 + if A.val = 0 then 1/2 else 0 := by
    have hz : (A.val : ZMod q) = 0 ↔ A.val = 0 := by
      rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
        Nat.mod_eq_of_lt A.isLt]
    unfold centeredSawtooth
    rw [if_congr hz rfl rfl, ZMod.val_natCast, Nat.mod_eq_of_lt A.isLt]
    split_ifs with ha
    · simp [ha]
    · ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hcorrection, hbase]
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumj]
  field_simp [hqC, hLC]
  ring

theorem sawtooth_product_fiber {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 0 < q) (hL : 0 < L) (t : ZMod q) :
    (∑ x : ZMod (q * L),
      if ZMod.castHom (Nat.dvd_mul_right q L) (ZMod q) x = t
        then centeredSawtooth x else 0) = centeredSawtooth t := by
  classical
  let e : Fin L × Fin q ≃ Fin (q * L) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm L q))
  have hz (ij : Fin L × Fin q) :
      ZMod.finEquiv (q * L) (e ij) =
        ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * L)) := by
    rw [finEquiv_eq_natCast]
    congr 1
  calc
    _ = ∑ ij : Fin L × Fin q,
        if (ij.2.val : ZMod q) = t then
          centeredSawtooth ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * L))
        else 0 := by
      symm
      apply Fintype.sum_equiv (e.trans (ZMod.finEquiv (q * L)).toEquiv)
      intro ij
      simp only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hz]
      simp
    _ = ∑ A : Fin q, if (A.val : ZMod q) = t then
        (∑ j : Fin L,
          centeredSawtooth ((A.val + q * j.val : ℕ) : ZMod (q * L))) else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      split_ifs <;> simp
    _ = ∑ A : Fin q, if (A.val : ZMod q) = t then
        centeredSawtooth (A.val : ZMod q) else 0 := by
      simp_rw [sawtooth_fin_fiber hq hL]
    _ = ∑ x : ZMod q, if x = t then centeredSawtooth x else 0 := by
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro A
      simp [finEquiv_eq_natCast]
    _ = _ := by simp

theorem sawtooth_reduction_fiber {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (t : ZMod q) :
    (∑ x : ZMod d, if ZMod.castHom hqd (ZMod q) x = t
      then centeredSawtooth x else 0) = centeredSawtooth t := by
  obtain ⟨L, rfl⟩ := hqd
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : 0 < L := by
    have h := NeZero.ne (q * L)
    by_contra hn
    have hzero : L = 0 := by omega
    simp [hzero] at h
  exact sawtooth_product_fiber hq hL t

def reduceUnit {q d : ℕ} (hqd : q ∣ d) (a : UnitClass d) : UnitClass q :=
  Units.map (ZMod.castHom hqd (ZMod q)).toMonoidHom a

theorem twisted_sawtooth_fiber {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (a : UnitClass d) (t : ZMod q) :
    (∑ x : ZMod d, if ZMod.castHom hqd (ZMod q) x = t
      then centeredSawtooth (a.val * x) else 0) =
      centeredSawtooth ((reduceUnit hqd a).val * t) := by
  classical
  let π := ZMod.castHom hqd (ZMod q)
  have hcancel (x : ZMod d) : a.val * (a⁻¹.val * x) = x := by
    rw [← mul_assoc, ← Units.val_mul]
    simp
  have hcondition (x : ZMod d) :
      π (a⁻¹.val * x) = t ↔ π x = (reduceUnit hqd a).val * t := by
    change π (a⁻¹.val * x) = t ↔ π x = π a.val * t
    constructor
    · intro hx
      rw [← hx, ← map_mul, hcancel]
    · intro hx
      rw [map_mul, hx, ← mul_assoc, ← map_mul, ← Units.val_mul]
      simp
  have hreindex := Equiv.sum_comp (a⁻¹.mulLeft)
    (fun x : ZMod d => if π x = t then centeredSawtooth (a.val * x) else 0)
  change (∑ x : ZMod d, if π x = t then centeredSawtooth (a.val * x) else 0) = _
  rw [← hreindex]
  calc
    _ = ∑ x : ZMod d, if π x = (reduceUnit hqd a).val * t
        then centeredSawtooth x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      change (if π (a⁻¹.val * x) = t then
        centeredSawtooth (a.val * (a⁻¹.val * x)) else 0) = _
      rw [hcancel, if_congr (hcondition x) rfl rfl]
    _ = _ := sawtooth_reduction_fiber hqd _

end NField.Alignment.CollisionSawtoothDistribution
