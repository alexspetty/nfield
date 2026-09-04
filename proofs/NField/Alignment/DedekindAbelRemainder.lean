/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindFourierMoment
import Mathlib.Data.Nat.Periodic

/-!
# Abel bounds for periodic Dedekind residues

This file isolates the analytic remainder in the cubic collision law.  A
Dedekind sum is sampled along a periodic unit-ratio orbit.  The orbit has
exact mean zero, its incomplete periods are controlled by the absolute first
moment, and a finite layer decomposition supplies the required monotone
weight estimate.
-/

namespace NField.Alignment.DedekindAbelRemainder

open scoped BigOperators ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindFourierMoment

/-- The Dedekind correlation attached to the residue of `a` modulo `k`.
Nonunits contribute zero, so this is a total periodic sequence. -/
noncomputable def residueDedekindSequence
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (a : ℕ) : ℂ :=
  if h : IsUnit (a : ZMod k) then
    dedekindSum (β * h.unit⁻¹)
  else 0

theorem residueDedekindSequence_add_period
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (a : ℕ) :
    residueDedekindSequence β (a + k) =
      residueDedekindSequence β a := by
  unfold residueDedekindSequence
  rw [Nat.cast_add, ZMod.natCast_self, add_zero]

theorem residueDedekindSequence_periodic
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) :
    Function.Periodic (residueDedekindSequence β) k :=
  residueDedekindSequence_add_period β

/-- Modulus two has only the identity unit. -/
theorem zmodTwo_unit_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  apply Units.val_injective
  apply ZMod.val_injective 2
  have hpos : 0 < u.val.val := ZMod.val_pos.mpr (IsUnit.ne_zero u.isUnit)
  have hlt : u.val.val < 2 := u.val.val_lt
  have hone : u.val.val = 1 := by omega
  rw [hone]
  rw [Units.val_one, ZMod.val_one 2]

/-- Every Dedekind sum at modulus two vanishes. -/
theorem dedekindSum_zmodTwo (u : (ZMod 2)ˣ) : dedekindSum u = 0 := by
  rw [zmodTwo_unit_eq_one u]
  simpa using dedekindSum_one (m := 2) (by omega)

theorem residueDedekindSequence_zmodTwo
    (β : (ZMod 2)ˣ) (a : ℕ) : residueDedekindSequence β a = 0 := by
  unfold residueDedekindSequence
  split
  · exact dedekindSum_zmodTwo _
  · rfl

/-- Over one complete residue interval the total absolute mass is exactly the
unit-group first moment. -/
theorem residueDedekindSequence_norm_period
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) :
    (∑ a ∈ Finset.range k, ‖residueDedekindSequence β a‖) =
      dedekindFirstMoment k := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod k)) IsUnit
      (fun x => if h : IsUnit x then ‖dedekindSum (β * h.unit⁻¹)‖ else 0)
  have hnonunit :
      (∑ x ∈ (Finset.univ : Finset (ZMod k)) with ¬IsUnit x,
        if h : IsUnit x then ‖dedekindSum (β * h.unit⁻¹)‖ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  calc
    (∑ a ∈ Finset.range k, ‖residueDedekindSequence β a‖) =
        ∑ a : Fin k, ‖residueDedekindSequence β a.val‖ := by
          exact (Fin.sum_univ_eq_sum_range
            (fun a : ℕ => ‖residueDedekindSequence β a‖) k).symm
    _ = ∑ x : ZMod k,
          if h : IsUnit x then ‖dedekindSum (β * h.unit⁻¹)‖ else 0 := by
          rw [← (ZMod.finEquiv k).toEquiv.sum_comp]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [show ((ZMod.finEquiv k).toEquiv a : ZMod k) =
              (a.val : ZMod k) by
            simpa using
              NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast a]
          unfold residueDedekindSequence
          split <;> simp_all
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod k)) with IsUnit x,
          if h : IsUnit x then ‖dedekindSum (β * h.unit⁻¹)‖ else 0 := by
          rw [← hpartition, hnonunit, add_zero]
    _ = ∑ x : {x : ZMod k // IsUnit x},
          ‖dedekindSum (β * x.property.unit⁻¹)‖ := by
          rw [show
            (∑ x ∈ (Finset.univ : Finset (ZMod k)) with IsUnit x,
              if h : IsUnit x then ‖dedekindSum (β * h.unit⁻¹)‖ else 0) =
              ∑ x : {x : ZMod k // IsUnit x},
                (if h : IsUnit x.val then
                  ‖dedekindSum (β * h.unit⁻¹)‖ else 0) by
            exact Finset.sum_subtype
              ((Finset.univ : Finset (ZMod k)).filter IsUnit)
              (by intro x; simp)
              (fun x => if h : IsUnit x then
                ‖dedekindSum (β * h.unit⁻¹)‖ else 0)]
          apply Finset.sum_congr rfl
          intro x _hx
          simp only [dif_pos x.property]
    _ = ∑ u : (ZMod k)ˣ, ‖dedekindSum (β * u⁻¹)‖ := by
          symm
          apply Fintype.sum_equiv unitsEquivIsUnit
          intro u
          have hunit :
              (unitsEquivIsUnit (m := k) u).property.unit = u := by
            apply Units.val_injective
            exact (unitsEquivIsUnit (m := k) u).property.unit_spec
          rw [hunit]
    _ = ∑ u : (ZMod k)ˣ, ‖dedekindSum u‖ := by
          let e : (ZMod k)ˣ ≃ (ZMod k)ˣ :=
            (Equiv.inv ((ZMod k)ˣ)).trans (Equiv.mulLeft β)
          exact e.sum_comp (fun u : (ZMod k)ˣ => ‖dedekindSum u‖)
    _ = dedekindFirstMoment k := rfl

/-- A complete period has exact signed sum zero. -/
theorem residueDedekindSequence_sum_period
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (β : (ZMod k)ˣ) :
    (∑ a ∈ Finset.range k, residueDedekindSequence β a) = 0 := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod k)) IsUnit
      (fun x => if h : IsUnit x then dedekindSum (β * h.unit⁻¹) else 0)
  have hnonunit :
      (∑ x ∈ (Finset.univ : Finset (ZMod k)) with ¬IsUnit x,
        if h : IsUnit x then dedekindSum (β * h.unit⁻¹) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  calc
    (∑ a ∈ Finset.range k, residueDedekindSequence β a) =
        ∑ a : Fin k, residueDedekindSequence β a.val := by
          exact (Fin.sum_univ_eq_sum_range
            (fun a : ℕ => residueDedekindSequence β a) k).symm
    _ = ∑ x : ZMod k,
          if h : IsUnit x then dedekindSum (β * h.unit⁻¹) else 0 := by
          rw [← (ZMod.finEquiv k).toEquiv.sum_comp]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [show ((ZMod.finEquiv k).toEquiv a : ZMod k) =
              (a.val : ZMod k) by
            simpa using
              NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast a]
          unfold residueDedekindSequence
          split <;> simp_all
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod k)) with IsUnit x,
          if h : IsUnit x then dedekindSum (β * h.unit⁻¹) else 0 := by
          rw [← hpartition, hnonunit, add_zero]
    _ = ∑ x : {x : ZMod k // IsUnit x},
          dedekindSum (β * x.property.unit⁻¹) := by
          rw [show
            (∑ x ∈ (Finset.univ : Finset (ZMod k)) with IsUnit x,
              if h : IsUnit x then dedekindSum (β * h.unit⁻¹) else 0) =
              ∑ x : {x : ZMod k // IsUnit x},
                (if h : IsUnit x.val then
                  dedekindSum (β * h.unit⁻¹) else 0) by
            exact Finset.sum_subtype
              ((Finset.univ : Finset (ZMod k)).filter IsUnit)
              (by intro x; simp)
              (fun x => if h : IsUnit x then
                dedekindSum (β * h.unit⁻¹) else 0)]
          apply Finset.sum_congr rfl
          intro x _hx
          simp only [dif_pos x.property]
    _ = ∑ u : (ZMod k)ˣ, dedekindSum (β * u⁻¹) := by
          symm
          apply Fintype.sum_equiv unitsEquivIsUnit
          intro u
          have hunit :
              (unitsEquivIsUnit (m := k) u).property.unit = u := by
            apply Units.val_injective
            exact (unitsEquivIsUnit (m := k) u).property.unit_spec
          rw [hunit]
    _ = ∑ u : (ZMod k)ˣ, dedekindSum u := by
          let e : (ZMod k)ˣ ≃ (ZMod k)ˣ :=
            (Equiv.inv ((ZMod k)ˣ)).trans (Equiv.mulLeft β)
          exact e.sum_comp dedekindSum
    _ = 0 := sum_dedekindSum_units_zero hk

theorem residueDedekindSequence_sum_period_of_two
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) (β : (ZMod k)ˣ) :
    (∑ a ∈ Finset.range k, residueDedekindSequence β a) = 0 := by
  by_cases hk2 : k = 2
  · subst k
    simp_rw [residueDedekindSequence_zmodTwo]
    simp
  · exact residueDedekindSequence_sum_period (by omega : 3 ≤ k) β

/-! ## Uniform bounds for incomplete periods -/

/-- A periodic sum splits into complete periods and a terminal prefix. -/
theorem periodic_sum_range_mul_add
    {k : ℕ} (f : ℕ → ℂ) (hf : Function.Periodic f k)
    (q r : ℕ) :
    (∑ a ∈ Finset.range (q * k + r), f a) =
      q • (∑ a ∈ Finset.range k, f a) +
        ∑ a ∈ Finset.range r, f a := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul]
      rw [show q * k + k + r = k + (q * k + r) by omega]
      rw [Finset.sum_range_add]
      have hshift (a : ℕ) : f (k + a) = f a := by
        simpa [Nat.add_comm] using hf a
      simp_rw [hshift]
      rw [ih, succ_nsmul]
      abel

/-- If a period has mean zero, every prefix is controlled by the absolute
mass of one period. -/
theorem norm_periodic_zeroMean_prefix_le
    {k : ℕ} (hk : 0 < k) (f : ℕ → ℂ)
    (hf : Function.Periodic f k)
    (hzero : (∑ a ∈ Finset.range k, f a) = 0) (n : ℕ) :
    ‖∑ a ∈ Finset.range n, f a‖ ≤
      ∑ a ∈ Finset.range k, ‖f a‖ := by
  have hdecomp := periodic_sum_range_mul_add f hf (n / k) (n % k)
  rw [Nat.div_add_mod'] at hdecomp
  rw [hdecomp, hzero, nsmul_zero, zero_add]
  calc
    ‖∑ a ∈ Finset.range (n % k), f a‖ ≤
        ∑ a ∈ Finset.range (n % k), ‖f a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range k, ‖f a‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        simp only [Finset.mem_range] at ha ⊢
        exact ha.trans (Nat.mod_lt n hk)
      · intro a _ha _hsmall
        positivity

/-- Every finite interval of a zero-mean periodic sequence is bounded by
twice the mass of one period. -/
theorem norm_periodic_zeroMean_interval_le
    {k : ℕ} (hk : 0 < k) (f : ℕ → ℂ)
    (hf : Function.Periodic f k)
    (hzero : (∑ a ∈ Finset.range k, f a) = 0)
    {s t : ℕ} (hst : s ≤ t) :
    ‖∑ a ∈ Finset.Ico s t, f a‖ ≤
      2 * ∑ a ∈ Finset.range k, ‖f a‖ := by
  rw [Finset.sum_Ico_eq_sub _ hst]
  calc
    ‖(∑ a ∈ Finset.range t, f a) -
        ∑ a ∈ Finset.range s, f a‖ ≤
        ‖∑ a ∈ Finset.range t, f a‖ +
          ‖∑ a ∈ Finset.range s, f a‖ := norm_sub_le _ _
    _ ≤ (∑ a ∈ Finset.range k, ‖f a‖) +
          ∑ a ∈ Finset.range k, ‖f a‖ := by
            gcongr
            · exact norm_periodic_zeroMean_prefix_le hk f hf hzero t
            · exact norm_periodic_zeroMean_prefix_le hk f hf hzero s
    _ = 2 * ∑ a ∈ Finset.range k, ‖f a‖ := by ring

/-- Applied to the Dedekind residue sequence, every interval is bounded by
twice the exact first moment. -/
theorem norm_residueDedekindSequence_interval_le
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (β : (ZMod k)ˣ)
    {s t : ℕ} (hst : s ≤ t) :
    ‖∑ a ∈ Finset.Ico s t, residueDedekindSequence β a‖ ≤
      2 * dedekindFirstMoment k := by
  simpa [residueDedekindSequence_norm_period β] using
    norm_periodic_zeroMean_interval_le (by omega : 0 < k)
      (residueDedekindSequence β)
      (residueDedekindSequence_periodic β)
      (residueDedekindSequence_sum_period hk β) hst

/-! ## Finite Abel summation -/

/-- A nonnegative antitone weight costs at most twice its initial value when
all global partial sums are uniformly bounded.  This is the finite Abel
estimate used below. -/
theorem norm_antitone_weighted_sum_le
    (w : ℕ → ℝ) (g : ℕ → ℂ)
    (hw0 : ∀ n, 0 ≤ w n) (hw : Antitone w)
    (M : ℝ) (hM : 0 ≤ M)
    (hprefix : ∀ n, ‖∑ i ∈ Finset.range n, g i‖ ≤ M)
    {s t : ℕ} :
    ‖∑ i ∈ Finset.Ico s t, w i • g i‖ ≤ 2 * w s * M := by
  by_cases hst : s < t
  · let G := fun n : ℕ => ∑ i ∈ Finset.range n, g i
    have hlast : s ≤ t - 1 := Nat.le_sub_one_of_lt hst
    have hdiff (i : ℕ) : 0 ≤ w i - w (i + 1) := by
      exact sub_nonneg.mpr (hw (Nat.le_succ i))
    have htel :
        (∑ i ∈ Finset.Ico s (t - 1), (w i - w (i + 1))) =
          w s - w (t - 1) := by
      rw [Finset.sum_sub_distrib]
      have hshift :
          (∑ i ∈ Finset.Ico (s + 1) t, w i) =
            ∑ i ∈ Finset.Ico s (t - 1), w (i + 1) := by
        rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hst),
          ← Finset.sum_Ico_add']
        simp only [add_tsub_cancel_right]
      rw [← hshift]
      have ht : t - 1 + 1 = t := Nat.sub_add_cancel (Nat.one_le_of_lt hst)
      calc
        (∑ i ∈ Finset.Ico s (t - 1), w i) -
            ∑ i ∈ Finset.Ico (s + 1) t, w i =
          ((∑ i ∈ Finset.Ico s t, w i) - w (t - 1)) -
            ((∑ i ∈ Finset.Ico s t, w i) - w s) := by
              rw [Finset.sum_Ico_sub_bot w hst]
              rw [← Finset.sum_Ico_succ_sub_top w hlast, ht]
        _ = w s - w (t - 1) := by ring
    have hA : ‖w (t - 1) • G t‖ ≤ w (t - 1) * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 (t - 1))]
      exact mul_le_mul_of_nonneg_left (hprefix t) (hw0 (t - 1))
    have hB : ‖w s • G s‖ ≤ w s * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 s)]
      exact mul_le_mul_of_nonneg_left (hprefix s) (hw0 s)
    have hC :
        ‖∑ i ∈ Finset.Ico s (t - 1),
            (w (i + 1) - w i) • G (i + 1)‖ ≤
          ∑ i ∈ Finset.Ico s (t - 1), (w i - w (i + 1)) * M := by
      calc
        ‖∑ i ∈ Finset.Ico s (t - 1),
            (w (i + 1) - w i) • G (i + 1)‖ ≤
            ∑ i ∈ Finset.Ico s (t - 1),
              ‖(w (i + 1) - w i) • G (i + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ico s (t - 1),
              (w i - w (i + 1)) * M := by
                apply Finset.sum_le_sum
                intro i _hi
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i)))]
                rw [neg_sub]
                exact mul_le_mul_of_nonneg_left (hprefix (i + 1)) (hdiff i)
    rw [Finset.sum_Ico_by_parts w g hst]
    change ‖w (t - 1) • G t - w s • G s -
        ∑ i ∈ Finset.Ico s (t - 1),
          (w (i + 1) - w i) • G (i + 1)‖ ≤ _
    calc
      _ ≤ ‖w (t - 1) • G t‖ + ‖w s • G s‖ +
          ‖∑ i ∈ Finset.Ico s (t - 1),
            (w (i + 1) - w i) • G (i + 1)‖ := by
              calc
                ‖(w (t - 1) • G t - w s • G s) -
                    ∑ i ∈ Finset.Ico s (t - 1),
                      (w (i + 1) - w i) • G (i + 1)‖ ≤
                    ‖w (t - 1) • G t - w s • G s‖ +
                      ‖∑ i ∈ Finset.Ico s (t - 1),
                        (w (i + 1) - w i) • G (i + 1)‖ := norm_sub_le _ _
                _ ≤ _ := by
                  simpa [add_assoc, add_comm, add_left_comm] using
                    add_le_add_right
                      (norm_sub_le (w (t - 1) • G t) (w s • G s))
                      ‖∑ i ∈ Finset.Ico s (t - 1),
                        (w (i + 1) - w i) • G (i + 1)‖
      _ ≤ w (t - 1) * M + w s * M +
          ∑ i ∈ Finset.Ico s (t - 1), (w i - w (i + 1)) * M := by
            gcongr
      _ = 2 * w s * M := by
            rw [← Finset.sum_mul, htel]
            ring
  · rw [Finset.Ico_eq_empty hst, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (hw0 s)) hM

/-- A shifted floor quotient, viewed as a real Abel weight. -/
noncomputable def shiftedFloorWeight (N s n : ℕ) : ℝ :=
  ((N / (s + n) : ℕ) : ℝ)

theorem shiftedFloorWeight_nonneg (N s n : ℕ) :
    0 ≤ shiftedFloorWeight N s n := by
  unfold shiftedFloorWeight
  positivity

theorem shiftedFloorWeight_antitone
    {N s : ℕ} (hs : 0 < s) : Antitone (shiftedFloorWeight N s) := by
  intro i j hij
  unfold shiftedFloorWeight
  exact_mod_cast Nat.div_le_div_left (Nat.add_le_add_left hij s)
    (Nat.add_pos_left hs i)

/-- A direct Abel interface for a floor-weighted Dedekind slice.  Any
uniform bound `M` for all interval prefixes gives the exact factor-two
weighted estimate used by sharper carrier arguments. -/
theorem norm_floorWeighted_residueDedekindSequence_le_of_prefix
    {k b : ℕ} [NeZero k] (hkb : k < b)
    (β : (ZMod k)ˣ) (M : ℝ) (hM : 0 ≤ M)
    (hprefix : ∀ start length,
      ‖∑ a ∈ Finset.Ico start (start + length),
          residueDedekindSequence β a‖ ≤ M) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      2 * (((b - 1) / (k + 1) : ℕ) : ℝ) * M := by
  let s := k + 1
  let n := b - s
  let g := fun j : ℕ => residueDedekindSequence β (s + j)
  let w := shiftedFloorWeight (b - 1) s
  have hs : 0 < s := by unfold s; omega
  have hsb : s ≤ b := by unfold s; omega
  have hn : s + n = b := by unfold n; omega
  have hglobal : ∀ r, ‖∑ j ∈ Finset.range r, g j‖ ≤ M := by
    intro r
    have h := hprefix s r
    rw [Finset.sum_Ico_eq_sum_range] at h
    simpa [g] using h
  have habel := norm_antitone_weighted_sum_le w g
    (shiftedFloorWeight_nonneg (b - 1) s)
    (shiftedFloorWeight_antitone hs) M hM hglobal (s := 0) (t := n)
  have hsum :
      (∑ a ∈ Finset.Ico s b,
          (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a) =
        ∑ j ∈ Finset.Ico 0 n, w j • g j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.Ico_zero_eq_range]
    change (∑ j ∈ Finset.range n,
        (((b - 1) / (s + j) : ℕ) : ℝ) •
          residueDedekindSequence β (s + j)) =
      ∑ j ∈ Finset.range n, w j • g j
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [show k + 1 = s by rfl, hsum]
  calc
    ‖∑ j ∈ Finset.Ico 0 n, w j • g j‖ ≤ 2 * w 0 * M := habel
    _ = 2 * (((b - 1) / (k + 1) : ℕ) : ℝ) * M := by
      unfold w shiftedFloorWeight s
      simp

/-- The floor-weighted Dedekind slice has the precise harmonic scale required
by the cubic law.  The factor four is an explicit Abel constant. -/
theorem norm_floorWeighted_residueDedekindSequence_le
    {k b : ℕ} [NeZero k] (hk : 3 ≤ k) (hkb : k < b)
    (β : (ZMod k)ˣ) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        dedekindFirstMoment k := by
  let s := k + 1
  let n := b - s
  let g := fun j : ℕ => residueDedekindSequence β (s + j)
  let w := shiftedFloorWeight (b - 1) s
  have hs : 0 < s := by unfold s; omega
  have hsb : s ≤ b := by unfold s; omega
  have hn : s + n = b := by unfold n; omega
  have hM : 0 ≤ 2 * dedekindFirstMoment k := by
    unfold dedekindFirstMoment
    positivity
  have hprefix : ∀ r, ‖∑ j ∈ Finset.range r, g j‖ ≤
      2 * dedekindFirstMoment k := by
    intro r
    have hinterval := norm_residueDedekindSequence_interval_le hk β
      (Nat.le_add_right s r)
    rw [Finset.sum_Ico_eq_sum_range] at hinterval
    simpa [g] using hinterval
  have habel := norm_antitone_weighted_sum_le w g
    (shiftedFloorWeight_nonneg (b - 1) s)
    (shiftedFloorWeight_antitone hs)
    (2 * dedekindFirstMoment k) hM hprefix (s := 0) (t := n)
  have hsum :
      (∑ a ∈ Finset.Ico s b,
          (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a) =
        ∑ j ∈ Finset.Ico 0 n, w j • g j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.Ico_zero_eq_range]
    change (∑ j ∈ Finset.range n,
        (((b - 1) / (s + j) : ℕ) : ℝ) •
          residueDedekindSequence β (s + j)) =
      ∑ j ∈ Finset.range n, w j • g j
    apply Finset.sum_congr rfl
    intro j _hj
    rfl
  rw [show k + 1 = s by rfl, hsum]
  calc
    ‖∑ j ∈ Finset.Ico 0 n, w j • g j‖ ≤
        2 * w 0 * (2 * dedekindFirstMoment k) := habel
    _ = 4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
          dedekindFirstMoment k := by
            unfold w shiftedFloorWeight s
            simp
            ring

/-- The same floor-weighted estimate including the zero modulus-two edge. -/
theorem norm_floorWeighted_residueDedekindSequence_le_of_two
    {k b : ℕ} [NeZero k] (hk : 2 ≤ k) (hkb : k < b)
    (β : (ZMod k)ˣ) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        dedekindFirstMoment k := by
  by_cases hk2 : k = 2
  · subst k
    simp_rw [residueDedekindSequence_zmodTwo]
    simp
    unfold dedekindFirstMoment
    positivity
  · exact norm_floorWeighted_residueDedekindSequence_le
      (by omega : 3 ≤ k) hkb β

end NField.Alignment.DedekindAbelRemainder
