/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthSawtooth

/-!
# Endpoint normalization

Exact arithmetic comparison between the sawtooth-normalized carry observable
and the centered floor-carry table. The discrepancy consists only of the two
cyclic endpoint cells, and a separate theorem proves that any such unitwise
constant is invisible to every nonprincipal character.
-/

namespace NField.Alignment.EndpointNormalization

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra

/-- The zero-or-one floor carry across cell n. -/
def carryStep (m A n : ℕ) : ℕ :=
  (n + 1) * A / m - n * A / m

/-- Quotient-remainder identity converting a residue jump into a floor carry. -/
theorem carryStep_quotient_identity
    {m A n : ℕ} (hm : 0 < m) :
    ((((n + 1) * A) % m : ℕ) : ℂ) / (m : ℂ) -
        (((n * A) % m : ℕ) : ℂ) / (m : ℂ) =
      (A : ℂ) / (m : ℂ) - (carryStep m A n : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqle : n * A / m ≤ (n + 1) * A / m :=
    Nat.div_le_div_right (Nat.mul_le_mul_right A (Nat.le_succ n))
  have h0 := Nat.mod_add_div (n * A) m
  have h1 := Nat.mod_add_div ((n + 1) * A) m
  have h0C : (((n * A) % m : ℕ) : ℂ) +
      (m : ℂ) * (((n * A / m : ℕ)) : ℂ) = ((n * A : ℕ) : ℂ) := by
    exact_mod_cast h0
  have h1C : ((((n + 1) * A) % m : ℕ) : ℂ) +
      (m : ℂ) * ((((n + 1) * A / m : ℕ)) : ℂ) =
        (((n + 1) * A : ℕ) : ℂ) := by
    exact_mod_cast h1
  unfold carryStep
  rw [Nat.cast_sub hqle]
  field_simp [hmC]
  push_cast at h0C h1C ⊢
  linear_combination h1C - h0C

/-- Multiplication by a unit residue cannot send an interior cell index to zero. -/
theorem natCast_mul_ne_zero
    {m A n : ℕ} [NeZero m] (hcop : A.Coprime m)
    (hnpos : 0 < n) (hnm : n < m) :
    ((n * A : ℕ) : ZMod m) ≠ 0 := by
  intro hz
  have hdvd : m ∣ n * A := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hmn : m ∣ n := hcop.symm.dvd_of_dvd_mul_right hdvd
  have hle := Nat.le_of_dvd hnpos hmn
  omega

/-- Title: `Sawtooth carry identity with endpoint corrections`.

Pointwise carry identity, including both cyclic endpoint corrections. -/
theorem sawtooth_carry_step
    {m A n : ℕ} [NeZero m]
    (hm : 2 ≤ m) (hApos : 1 ≤ A) (hAm : A < m)
    (hcop : A.Coprime m) (hn : n < m) :
    -(centeredSawtooth (((n + 1) * A : ℕ) : ZMod m) -
        centeredSawtooth ((n * A : ℕ) : ZMod m)) =
      (carryStep m A n : ℂ) - (A : ℂ) / (m : ℂ) +
        (if n = 0 then (1 / 2 : ℂ)
         else if n = m - 1 then -(1 / 2 : ℂ) else 0) := by
  have hmpos : 0 < m := by omega
  by_cases hn0 : n = 0
  · subst n
    unfold centeredSawtooth carryStep
    simp only [zero_mul, Nat.zero_div, Nat.cast_zero,
      zero_add, one_mul, sub_zero, if_pos]
    have hAcast : (A : ZMod m) ≠ 0 := by
      intro hz
      have hdvd := (ZMod.natCast_eq_zero_iff A m).mp hz
      have hle := Nat.le_of_dvd hApos hdvd
      omega
    rw [if_neg hAcast, ZMod.val_natCast, Nat.mod_eq_of_lt hAm]
    have hdiv : A / m = 0 := Nat.div_eq_of_lt hAm
    rw [hdiv]
    push_cast
    ring
  · by_cases hnlast : n = m - 1
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn1 : n + 1 = m := by omega
      have hprev : ((n * A : ℕ) : ZMod m) ≠ 0 :=
        natCast_mul_ne_zero hcop hnpos hn
      unfold centeredSawtooth
      rw [if_pos (by simp [hn1]), if_neg hprev]
      rw [ZMod.val_natCast]
      have hcorr :
          (if n = 0 then (1 / 2 : ℂ)
           else if n = m - 1 then -(1 / 2 : ℂ) else 0) = -(1 / 2) := by
        have hm1 : m - 1 ≠ 0 := by omega
        simp [hnlast, hm1]
      rw [hcorr]
      have hq := carryStep_quotient_identity (A := A) (n := n) hmpos
      rw [hn1] at hq
      simp only [Nat.mul_mod_right, Nat.cast_zero, zero_div] at hq
      calc
        -((0 : ℂ) - (((n * A % m : ℕ) : ℂ) / (m : ℂ) - 1 / 2)) =
            -((0 : ℂ) - ((n * A % m : ℕ) : ℂ) / (m : ℂ)) - 1 / 2 := by ring
        _ = -((A : ℂ) / (m : ℂ) - (carryStep m A n : ℂ)) - 1 / 2 := by rw [hq]
        _ = (carryStep m A n : ℂ) - (A : ℂ) / (m : ℂ) - 1 / 2 := by ring
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn1pos : 0 < n + 1 := Nat.succ_pos n
      have hn1lt : n + 1 < m := by omega
      have hleft : ((n * A : ℕ) : ZMod m) ≠ 0 :=
        natCast_mul_ne_zero hcop hnpos hn
      have hright : (((n + 1) * A : ℕ) : ZMod m) ≠ 0 :=
        natCast_mul_ne_zero hcop hn1pos hn1lt
      unfold centeredSawtooth
      rw [if_neg hright, if_neg hleft]
      rw [ZMod.val_natCast, ZMod.val_natCast]
      have hcorr :
          (if n = 0 then (1 / 2 : ℂ)
           else if n = m - 1 then -(1 / 2 : ℂ) else 0) = 0 := by
        simp [hn0, hnlast]
      rw [hcorr]
      have hq := carryStep_quotient_identity (A := A) (n := n) hmpos
      calc
        -(((((n + 1) * A) % m : ℕ) : ℂ) / (m : ℂ) - 1 / 2 -
            ((((n * A) % m : ℕ) : ℂ) / (m : ℂ) - 1 / 2)) =
            -(((((n + 1) * A) % m : ℕ) : ℂ) / (m : ℂ) -
              (((n * A) % m : ℕ) : ℂ) / (m : ℂ)) := by ring
        _ = -((A : ℂ) / (m : ℂ) - (carryStep m A n : ℂ)) := by rw [hq]
        _ = (carryStep m A n : ℂ) - (A : ℂ) / (m : ℂ) + 0 := by ring

/-- Weighted floor-carry table on canonical cell representatives. -/
noncomputable def naturalWeightedCarry
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (A : ℕ) : ℂ :=
  ∑ n : Fin m, (carryStep m A n.val : ℂ) * w (n.val : ZMod m)

/-- Total cell weight on canonical representatives. -/
noncomputable def naturalWeightTotal
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) : ℂ :=
  ∑ n : Fin m, w (n.val : ZMod m)

/-- Title: `Endpoint normalization`.

Exact endpoint normalization for every unit multiplier. -/
theorem endpoint_normalization
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : ZMod m → ℂ) (a : UnitClass m) :
    carryObservable w a.val =
      naturalWeightedCarry w a.val.val -
        (a.val.val : ℂ) / (m : ℂ) * naturalWeightTotal w +
        (1 / 2 : ℂ) * (w 0 - w (m - 1 : ℕ)) := by
  classical
  letI : Fact (1 < m) := ⟨by omega⟩
  let A := a.val.val
  have hApos : 1 ≤ A := by
    have hne : a.val ≠ 0 := by
      exact IsUnit.ne_zero a.isUnit
    exact (ZMod.val_pos.mpr hne)
  have hAm : A < m := a.val.val_lt
  have hcop : A.Coprime m := by
    have hunit : IsUnit (A : ZMod m) := by
      simpa only [A, ZMod.natCast_zmod_val] using a.isUnit
    exact (ZMod.isUnit_iff_coprime A m).mp hunit
  have haCast : (A : ZMod m) = a.val := ZMod.natCast_zmod_val a.val
  have hpoint (n : Fin m) :
      -(centeredSawtooth (((n.val + 1) * A : ℕ) : ZMod m) -
          centeredSawtooth ((n.val * A : ℕ) : ZMod m)) =
        (carryStep m A n.val : ℂ) - (A : ℂ) / (m : ℂ) +
          (if n.val = 0 then (1 / 2 : ℂ)
           else if n.val = m - 1 then -(1 / 2 : ℂ) else 0) :=
    sawtooth_carry_step hm hApos hAm hcop n.isLt
  let last : Fin m := ⟨m - 1, by omega⟩
  have hm1 : m - 1 ≠ 0 := by omega
  have hlastne : last ≠ (0 : Fin m) := by
    intro h
    have hv := congrArg Fin.val h
    simp [last] at hv
    omega
  have hzerolast : (0 : Fin m) ≠ last := hlastne.symm
  have hcorr (n : Fin m) :
      (if n.val = 0 then (1 / 2 : ℂ)
       else if n.val = m - 1 then -(1 / 2 : ℂ) else 0) =
      (if n = 0 then (1 / 2 : ℂ)
       else if n = last then -(1 / 2 : ℂ) else 0) := by
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnval0 : n.val ≠ 0 := by
        intro h
        exact hn0 (Fin.ext h)
      by_cases hnlast : n = last
      · subst n
        simp [last, hlastne, hm1]
      · have hnvalLast : n.val ≠ m - 1 := by
          intro h
          exact hnlast (Fin.ext h)
        simp [hn0, hnval0, hnlast, hnvalLast]
  unfold carryObservable naturalWeightedCarry naturalWeightTotal
  rw [show a.val = (A : ZMod m) by exact haCast.symm]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hAm]
  have hreindex :
      (∑ n : ZMod m, w n *
        (centeredSawtooth ((n + 1) * (A : ZMod m)) -
          centeredSawtooth (n * (A : ZMod m)))) =
      ∑ n : Fin m, w (n.val : ZMod m) *
        (centeredSawtooth (((n.val + 1) * A : ℕ) : ZMod m) -
          centeredSawtooth ((n.val * A : ℕ) : ZMod m)) := by
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv m).toEquiv
    intro n
    have hz : (ZMod.finEquiv m).toEquiv n = (n.val : ZMod m) :=
      NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast n
    rw [hz]
    congr 3 <;> push_cast <;> ring
  rw [hreindex, ← Finset.sum_neg_distrib]
  simp_rw [← mul_neg, hpoint]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [hcorr]
  have hend :
      (∑ n : Fin m, w (n.val : ZMod m) *
        (if n = 0 then (1 / 2 : ℂ)
         else if n = last then -(1 / 2 : ℂ) else 0)) =
        (1 / 2 : ℂ) * (w 0 - w (m - 1 : ℕ)) := by
    have hsplit (n : Fin m) :
        w (n.val : ZMod m) *
            (if n = 0 then (1 / 2 : ℂ)
             else if n = last then -(1 / 2 : ℂ) else 0) =
          (if n = 0 then w (n.val : ZMod m) * (1 / 2 : ℂ) else 0) +
          (if n = last then w (n.val : ZMod m) * (-(1 / 2 : ℂ)) else 0) := by
      by_cases hn0 : n = 0
      · subst n
        simp [hzerolast]
      · by_cases hnl : n = last
        · subst n
          simp [hlastne]
        · simp [hn0, hnl]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [last, mul_sub]
    ring
  rw [hend]
  have hcarrySum :
      (∑ n : Fin m, w (n.val : ZMod m) * (carryStep m A n.val : ℂ)) =
        ∑ n : Fin m, (carryStep m A n.val : ℂ) * w (n.val : ZMod m) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hbulkSum :
      (∑ n : Fin m, w (n.val : ZMod m) * ((A : ℂ) / (m : ℂ))) =
        ∑ n : Fin m, ((A : ℂ) / (m : ℂ)) * w (n.val : ZMod m) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hcarrySum, hbulkSum]
  ring

/-- Title: `Spectral invisibility of a constant on units`.

A constant discrepancy on units vanishes in every nonprincipal character channel. -/
theorem unit_constant_is_spectrally_invisible
    {m : ℕ} [NeZero m] (F A : ZMod m → ℂ) (c : ℂ)
    {ψ : Character m} (hψ : ψ ≠ 1)
    (hunit : ∀ u : UnitClass m, F u.val = A u.val + c) :
    (∑ x : ZMod m, F x * ψ x) = ∑ x : ZMod m, A x * ψ x := by
  classical
  have hsum : ∑ x : ZMod m, ψ x = 0 := ψ.sum_eq_zero_of_ne_one hψ
  calc
    (∑ x : ZMod m, F x * ψ x) =
      ∑ x : ZMod m, (A x + c) * ψ x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : IsUnit x
        · let u : UnitClass m := hx.unit
          have hu : u.val = x := hx.unit_spec
          rw [← hu, hunit]
        · rw [MulChar.map_nonunit ψ hx]
          ring
    _ = (∑ x : ZMod m, A x * ψ x) + c * ∑ x : ZMod m, ψ x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x : ZMod m, A x * ψ x := by rw [hsum, mul_zero, add_zero]

end NField.Alignment.EndpointNormalization
