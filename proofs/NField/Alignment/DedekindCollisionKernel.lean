/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthSawtooth

/-!
# The Dedekind collision kernel

The classical Dedekind sum is defined directly from the centered sawtooth on
`ZMod m`.  Keeping its first argument as a unit makes the hypotheses visible
in the type and gives the two exact symmetries used by collision-ratio
compression.
-/

namespace NField.Alignment.DedekindCollisionKernel

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthSawtooth

/-- The classical Dedekind sum in the manuscript's centered-sawtooth
normalization.  The zero residue contributes zero, so this is exactly the
usual sum over `1 <= a < m`. -/
noncomputable def dedekindSum
    {m : ℕ} [NeZero m] (h : UnitClass m) : ℂ :=
  ∑ x : ZMod m,
    centeredSawtooth x * centeredSawtooth (h.val * x)

/-- Negating the first argument negates the Dedekind sum. -/
theorem dedekindSum_neg
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) (h : UnitClass m) :
    dedekindSum (-h) = -dedekindSum h := by
  classical
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hmul : (-h : UnitClass m).val * x = -(h.val * x) := by
    simp
  rw [hmul, centeredSawtooth_neg hm]
  ring

/-- Inverting the first argument leaves the Dedekind sum unchanged. -/
theorem dedekindSum_inv
    {m : ℕ} [NeZero m] (h : UnitClass m) :
    dedekindSum h⁻¹ = dedekindSum h := by
  classical
  unfold dedekindSum
  let e : ZMod m ≃ ZMod m := h.mulLeft
  have hreindex := e.sum_comp
    (fun x : ZMod m =>
      centeredSawtooth x * centeredSawtooth (h⁻¹.val * x))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [e, Units.mulLeft]
  change centeredSawtooth ((h : ZMod m) * x) *
      centeredSawtooth ((h⁻¹ : UnitClass m).val * ((h : ZMod m) * x)) =
    centeredSawtooth x * centeredSawtooth ((h : ZMod m) * x)
  rw [← mul_assoc, ← Units.val_mul]
  simp [mul_comm]

/-- Multiplying numerator and denominator of a collision ratio by the same
unit does not change its Dedekind argument. -/
theorem unitRatio_cancel
    {m : ℕ} [NeZero m] (g k u : UnitClass m) :
    (g * k)⁻¹ * (g * u) = k⁻¹ * u := by
  group

/-- The corresponding Dedekind summand depends only on the reduced unit
ratio. -/
theorem dedekindSum_ratio_cancel
    {m : ℕ} [NeZero m] (g k u : UnitClass m) :
    dedekindSum ((g * k)⁻¹ * (g * u)) =
      dedekindSum (k⁻¹ * u) := by
  rw [unitRatio_cancel]

/-- Swapping the two coordinates of a collision ratio leaves its Dedekind
sum unchanged. -/
theorem dedekindSum_ratio_swap
    {m : ℕ} [NeZero m] (k u : UnitClass m) :
    dedekindSum (u⁻¹ * k) = dedekindSum (k⁻¹ * u) := by
  have hinv : (k⁻¹ * u)⁻¹ = u⁻¹ * k := by group
  rw [← hinv, dedekindSum_inv]

/-- The sum over all unit arguments vanishes by the fixed-point-free
reflection pairing available at every modulus at least three. -/
theorem sum_dedekindSum_units_zero
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    ∑ h : UnitClass m, dedekindSum h = 0 := by
  classical
  have hneg : ∀ h : UnitClass m, dedekindSum (-h) = -dedekindSum h :=
    dedekindSum_neg (by omega)
  have hreindex :
      (∑ h : UnitClass m, dedekindSum (-h)) =
        ∑ h : UnitClass m, dedekindSum h := by
    let e : UnitClass m ≃ UnitClass m := Equiv.neg _
    simpa [e] using e.sum_comp dedekindSum
  have hsumneg :
      (∑ h : UnitClass m, dedekindSum (-h)) =
        -∑ h : UnitClass m, dedekindSum h := by
    simp_rw [hneg]
    rw [Finset.sum_neg_distrib]
  have hself :
      (∑ h : UnitClass m, dedekindSum h) =
        -∑ h : UnitClass m, dedekindSum h :=
    hreindex.symm.trans hsumneg
  linear_combination (1 / 2 : ℂ) * hself

/-! ## The exact diagonal value -/

theorem complex_sum_range_id (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℂ) =
      (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem complex_sum_range_sq (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℂ) ^ 2 =
      (n : ℂ) * ((n : ℂ) - 1) * (2 * (n : ℂ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Closed evaluation of the ratio-one Dedekind sum. -/
theorem dedekindSum_one
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    dedekindSum (1 : UnitClass m) =
      ((m : ℂ) - 1) * ((m : ℂ) - 2) / (12 * (m : ℂ)) := by
  classical
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hreindex :
      dedekindSum (1 : UnitClass m) =
        ∑ a : Fin m,
          (if a.val = 0 then 0
           else ((a.val : ℂ) / (m : ℂ) - 1 / 2) ^ 2) := by
    unfold dedekindSum
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv m).toEquiv
    intro a
    have hfin : (ZMod.finEquiv m).toEquiv a = (a.val : ZMod m) := by
      simpa using finEquiv_eq_natCast a
    rw [hfin]
    simp only [Units.val_one, one_mul]
    by_cases ha : a.val = 0
    · rw [if_pos ha]
      have hazero : a = 0 := Fin.ext ha
      subst a
      simp [centeredSawtooth]
    · rw [if_neg ha]
      have hcast : (a.val : ZMod m) ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, ha] at hv
      unfold centeredSawtooth
      rw [if_neg hcast, ZMod.val_natCast,
        Nat.mod_eq_of_lt a.isLt]
      simp [pow_two]
  rw [hreindex]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      if i = 0 then (0 : ℂ)
      else ((i : ℂ) / (m : ℂ) - 1 / 2) ^ 2) m]
  have hpoint (i : ℕ) (hi : i ∈ Finset.range m) :
      (if i = 0 then (0 : ℂ)
       else ((i : ℂ) / (m : ℂ) - 1 / 2) ^ 2) =
        ((i : ℂ) / (m : ℂ) - 1 / 2) ^ 2 -
          if i = 0 then 1 / 4 else 0 := by
    by_cases hz : i = 0
    · subst i
      simp
      ring
    · simp [hz]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hcorrection :
      (∑ i ∈ Finset.range m, if i = 0 then (1 / 4 : ℂ) else 0) =
        1 / 4 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hne
      simp [hne]
    · simp [show 0 < m by omega]
  rw [hcorrection]
  have hexpand :
      (∑ i ∈ Finset.range m,
        ((i : ℂ) / (m : ℂ) - 1 / 2) ^ 2) =
        (m : ℂ)⁻¹ ^ 2 *
            ∑ i ∈ Finset.range m, (i : ℂ) ^ 2 -
          (m : ℂ)⁻¹ *
            ∑ i ∈ Finset.range m, (i : ℂ) +
          (m : ℂ) / 4 := by
    calc
      (∑ i ∈ Finset.range m,
          ((i : ℂ) / (m : ℂ) - 1 / 2) ^ 2) =
        ∑ i ∈ Finset.range m,
          ((m : ℂ)⁻¹ ^ 2 * (i : ℂ) ^ 2 -
            (m : ℂ)⁻¹ * (i : ℂ) + 1 / 4) := by
              apply Finset.sum_congr rfl
              intro i _
              field_simp [hm0]
              ring
      _ = (m : ℂ)⁻¹ ^ 2 *
            ∑ i ∈ Finset.range m, (i : ℂ) ^ 2 -
          (m : ℂ)⁻¹ *
            ∑ i ∈ Finset.range m, (i : ℂ) +
          (m : ℂ) / 4 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              simp
              ring
  rw [hexpand, complex_sum_range_sq, complex_sum_range_id]
  field_simp [hm0]
  ring

end NField.Alignment.DedekindCollisionKernel
