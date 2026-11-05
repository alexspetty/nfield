/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeBlockAtomless
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Absence of atoms in the actual potential law

A positive potential atom would have a positive-measure return under the
stationary odometer. Its block difference would be exactly zero on that
return set, contradicting the proved atomlessness of every nonempty block.
The quantitative one-quarter concentration estimate is a separate result.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialAtomless

open scoped Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialCoboundary
open CollisionPotentialConvergence CollisionPrimeBlockAtomless

theorem translate_one_iterate (n : ℕ) : (CollisionPotentialCoboundary.translate 1)^[n]=CollisionPotentialCoboundary.translate (n : ℤ) := by
  funext x
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using (translate_add 1 (n : ℤ) x).symm

theorem potential_atom_measure_zero (u : ℝ) : phaseHaar {x | collisionPotential x=u}=0 := by
  by_contra hu
  have hA : NullMeasurableSet {x : Phase | collisionPotential x=u} phaseHaar := by
    change NullMeasurableSet ((fun x : Phase => collisionPotential x) ⁻¹' {u}) phaseHaar
    exact (Lp.aestronglyMeasurable collisionPotential).aemeasurable.nullMeasurable
      (measurableSet_singleton u)
  have hc : Conservative (CollisionPotentialCoboundary.translate 1) phaseHaar :=
    (translate_measurePreserving 1).conservative
  have hret : ∃ h : ℕ, 0<h ∧ phaseHaar ({x : Phase | collisionPotential x=u} ∩
      (CollisionPotentialCoboundary.translate 1)^[h] ⁻¹' {x : Phase | collisionPotential x=u})≠0 :=
    hc.exists_gt_measure_inter_ne_zero (s := {x : Phase | collisionPotential x=u}) hA hu 0
  obtain ⟨h,hh,hpos⟩ := hret
  rw [translate_one_iterate] at hpos
  have hsub : ({x : Phase | collisionPotential x=u} ∩
      CollisionPotentialCoboundary.translate (h : ℤ) ⁻¹' {x : Phase | collisionPotential x=u} : Set Phase) ≤ᵐ[phaseHaar]
      ({x : Phase | blockFunction h x=0} : Set Phase) := by
    filter_upwards [block_telescope_ae h] with x hx
    rintro ⟨hx0,hxh⟩
    change collisionPotential x=u at hx0
    change collisionPotential (CollisionPotentialCoboundary.translate (h : ℤ) x)=u at hxh
    change blockFunction h x=0
    rw [hx,hx0,hxh,sub_self]
  exact hpos (le_antisymm ((measure_mono_ae hsub).trans
    (le_of_eq (incrementBlock_atom_measure_zero hh 0))) bot_le)

theorem potential_law_singleton (u : ℝ) : (Measure.map collisionPotential phaseHaar) {u}=0 := by
  rw [Measure.map_apply_of_aemeasurable (Lp.aestronglyMeasurable collisionPotential).aemeasurable
    (measurableSet_singleton u)]
  exact potential_atom_measure_zero u

end NField.Alignment.CollisionPotentialAtomless
