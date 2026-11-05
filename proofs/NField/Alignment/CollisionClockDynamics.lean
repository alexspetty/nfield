/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCycleStationarity
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The weighted clock state and its exact modular update

The orbit PMF uses the existing disjoint union of finite cycles. Its padded
period-one state has zero mass; the period-zero fiber is empty. On every
active cycle this is the literal pi_N and T from the manuscript.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionClockDynamics

open scoped BigOperators Classical ENNReal
open CollisionCycleStationarity CollisionRemainderDynamics CollisionMassReadout

def cycleRotation : Equiv.Perm CycleState := Equiv.sigmaCongrRight (fun k => finRotate k)

theorem cycleRotation_period (z : CycleState) : (cycleRotation z).1=z.1 := rfl

theorem cycleRotation_residue (z : CycleState) :
    (cycleRotation z).2.val=(z.2.val+1)%z.1 := by
  letI := z.2.neZero
  change (finRotate z.1 z.2).val=_
  rw [finRotate_apply]
  simp [Fin.add_def,Nat.add_mod]

theorem orbitPMF_literal (N : ℕ) (z : CycleState) :
    (orbitPMF N z).toReal=collisionWeight z.1*(if z.2.val=N%z.1 then 1 else 0) := by
  change (ENNReal.ofReal (orbitMass N z)).toReal=_
  rw [ENNReal.toReal_ofReal (orbitMass_nonneg N z)]
  by_cases h : N%z.1=z.2.val
  · simp only [orbitMass,if_pos h,if_pos h.symm,mul_one]
  · simp only [orbitMass,if_neg h,if_neg (Ne.symm h),mul_zero]

theorem orbitPMF_inactive_zero {z : CycleState} (hz : z.1 < 2) (N : ℕ) : orbitPMF N z=0 := by
  rcases z with ⟨k,r⟩
  change k < 2 at hz
  interval_cases k
  · exact r.elim0
  · change ENNReal.ofReal (orbitMass N ⟨1,r⟩)=0
    simp [orbitMass]

theorem remainder_rotation_equivalence (N : ℕ) (z : CycleState) :
    (N+1)%z.1=(cycleRotation z).2.val ↔ N%z.1=z.2.val := by
  rw [cycleRotation_residue]
  constructor
  · intro h
    have hm : Nat.ModEq z.1 (N+1) (z.2.val+1) := h
    have hc := hm.add_right_cancel' 1
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt z.2.isLt] using hc
  · intro h
    simp [Nat.add_mod,h,Nat.mod_eq_of_lt z.2.isLt]

theorem orbitMass_rotation (N : ℕ) (z : CycleState) :
    orbitMass (N+1) (cycleRotation z)=orbitMass N z := by
  change (if (N+1)%z.1=(cycleRotation z).2.val then collisionWeight z.1 else 0)=
    (if N%z.1=z.2.val then collisionWeight z.1 else 0)
  simp only [remainder_rotation_equivalence]

theorem orbitPMF_rotation (N : ℕ) (z : CycleState) :
    orbitPMF (N+1) (cycleRotation z)=orbitPMF N z := by
  change ENNReal.ofReal (orbitMass (N+1) (cycleRotation z))=ENNReal.ofReal (orbitMass N z)
  rw [orbitMass_rotation]

theorem orbitPMF_pushforward (N : ℕ) : (orbitPMF N).map cycleRotation=orbitPMF (N+1) := by
  ext z
  obtain ⟨y,rfl⟩ := cycleRotation.surjective z
  rw [PMF.map_apply,tsum_eq_single y]
  · simp [orbitPMF_rotation]
  · intro x hxy
    have he : cycleRotation y ≠ cycleRotation x := by
      intro he
      exact hxy (cycleRotation.injective he).symm
    simp [he]

theorem literal_clock_state_and_update (N : ℕ) :
    (∀ z : CycleState, (orbitPMF N z).toReal=
      collisionWeight z.1*(if z.2.val=N%z.1 then 1 else 0)) ∧
    (∀ z : CycleState, (cycleRotation z).1=z.1 ∧
      (cycleRotation z).2.val=(z.2.val+1)%z.1) ∧
    (orbitPMF N).map cycleRotation=orbitPMF (N+1) := by
  exact ⟨orbitPMF_literal N,fun z => ⟨cycleRotation_period z,cycleRotation_residue z⟩,
    orbitPMF_pushforward N⟩

end NField.Alignment.CollisionClockDynamics
