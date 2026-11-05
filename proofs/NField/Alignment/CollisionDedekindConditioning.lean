/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDedekindPairing

/-!
# Conditional sawtooth means and common-grid invariance

Conditional means use the actual Haar mass of a residue cylinder. The
common-grid energy of a fixed finite coefficient array equals its Haar
squared norm on every common multiple of the original row periods.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDedekindConditioning

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionCharacterStructure
open CarryBoundarySpectra CollisionSawtoothDistribution CollisionDedekindPairing
open CollisionCharacteristicCycles CollisionDivisibilityCovariance CollisionCylinderMeans

theorem twisted_cylinder_integral_complex {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (a : UnitClass d) (t : ZMod q) :
    (∫ x, if (residueHom q x).toAdd = t then
      centeredSawtooth (a.val * (residueHom d x).toAdd) else 0 ∂phaseHaar) =
      centeredSawtooth ((reduceUnit hqd a).val * t) / (d : ℂ) := by
  have hgrid (x : Phase) :
      (if (residueHom q x).toAdd = t then
        centeredSawtooth (a.val * (residueHom d x).toAdd) else 0) =
      (if ZMod.castHom hqd (ZMod q)
          ((residueHom d x).toAdd.val : ZMod d) = t then
        centeredSawtooth (a.val * ((residueHom d x).toAdd.val : ZMod d)) else 0) := by
    rw [ZMod.natCast_zmod_val, residue_compatible hqd]
  simp_rw [hgrid]
  rw [integral_residue_complex d
    (fun n => if ZMod.castHom hqd (ZMod q) (n : ZMod d) = t then
      centeredSawtooth (a.val * (n : ZMod d)) else 0),
    ← sum_zmod_val_complex]
  simp_rw [ZMod.natCast_zmod_val]
  rw [twisted_sawtooth_fiber]

theorem twisted_cylinder_integral {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (a : UnitClass d) (t : ZMod q) :
    (∫ x in residueEvent q t.val, twistedSawtooth a x ∂phaseHaar) =
      midpointSawtooth ((reduceUnit hqd a).val * t) / (d : ℝ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← integral_indicator (residueEvent_measurable q t.val)]
  have hpoint (x : Phase) :
      (residueEvent q t.val).indicator (twistedSawtooth a) x =
        if (residueHom q x).toAdd = t then twistedSawtooth a x else 0 := by
    simp [Set.indicator_apply, residueEvent, hq]
  simp_rw [hpoint]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, twistedSawtooth,
    apply_ite Complex.ofReal, Complex.ofReal_zero, midpointSawtooth_complex]
  exact twisted_cylinder_integral_complex hqd a t

theorem twisted_cylinder_mean {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (a : UnitClass d) (t : ZMod q) :
    (∫ x in residueEvent q t.val, twistedSawtooth a x ∂phaseHaar) /
      phaseHaar.real (residueEvent q t.val) =
        ((q : ℝ) / d) * midpointSawtooth ((reduceUnit hqd a).val * t) := by
  rw [twisted_cylinder_integral hqd, residueEvent_measure
    (Nat.pos_of_ne_zero (NeZero.ne q))]
  simp only [one_div, div_inv_eq_mul]
  ring

theorem twistedSawtooth_via_grid {d L : ℕ} [NeZero d] [NeZero L]
    (hdL : d ∣ L) (a : UnitClass d) (x : Phase) :
    twistedSawtooth a x =
      midpointSawtooth (a.val * ((residueHom L x).toAdd.val : ZMod d)) := by
  rw [twistedSawtooth, residue_compatible hdL]
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem finite_sawtooth_grid_energy {ι : Type*} [Fintype ι]
    (d : ι → ℕ) [∀ i, NeZero (d i)] (a : ∀ i, UnitClass (d i)) (c : ι → ℝ)
    {L : ℕ} [NeZero L] (hL : ∀ i, d i ∣ L) :
    (∫ x, (∑ i, c i * twistedSawtooth (a i) x) ^ 2 ∂phaseHaar) =
      (∑ n ∈ Finset.range L,
        (∑ i, c i * midpointSawtooth ((a i).val * (n : ZMod (d i)))) ^ 2) /
          (L : ℝ) := by
  have hrow (x : Phase) :
      (∑ i, c i * twistedSawtooth (a i) x) ^ 2 =
      (∑ i, c i * midpointSawtooth
        ((a i).val * ((residueHom L x).toAdd.val : ZMod (d i)))) ^ 2 := by
    simp_rw [twistedSawtooth_via_grid (hL _)]
  simp_rw [hrow]
  exact integral_residue L
    (fun n => (∑ i, c i * midpointSawtooth ((a i).val * (n : ZMod (d i)))) ^ 2)

theorem finite_sawtooth_grid_invariance {ι : Type*} [Fintype ι]
    (d : ι → ℕ) [∀ i, NeZero (d i)] (a : ∀ i, UnitClass (d i)) (c : ι → ℝ)
    {L K : ℕ} [NeZero L] [NeZero K] (hL : ∀ i, d i ∣ L) (hK : ∀ i, d i ∣ K) :
    (∑ n ∈ Finset.range L,
      (∑ i, c i * midpointSawtooth ((a i).val * (n : ZMod (d i)))) ^ 2) / (L : ℝ) =
    (∑ n ∈ Finset.range K,
      (∑ i, c i * midpointSawtooth ((a i).val * (n : ZMod (d i)))) ^ 2) / (K : ℝ) := by
  rw [← finite_sawtooth_grid_energy d a c hL, ← finite_sawtooth_grid_energy d a c hK]

end NField.Alignment.CollisionDedekindConditioning
