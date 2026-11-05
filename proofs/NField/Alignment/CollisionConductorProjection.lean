/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderMeans
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Projection onto complete finite conductor spaces

All residue directions at every admitted period are retained. The first
step proves that the full-amplitude cutoff has the same cylinder means as
the actual Haar potential for every such period.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorProjection

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionJordanVariance
open CollisionConductorRows CollisionCylinderMeans CollisionReciprocalBudget

theorem cylinderFunctional_primitiveRow {L q : ℕ} (hL : 0<L) (hq : 0<q) (a : ℕ) :
    cylinderFunctional L a (primitiveRow q)=if q∣L then primitiveValue q a else 0 := by
  apply divisor_sums_injective
    (fun d => cylinderFunctional L a (primitiveRow d))
    (fun d => if d∣L then primitiveValue d a else 0) _ q hq
  intro k hk
  rw [← map_sum,sum_primitiveRow_divisors hk,cylinderFunctional_remainder hk hL,Nat.gcd_comm]
  exact centered_gcd_primitive_sum hk L a

theorem cylinderFunctional_weightedRows {L : ℕ} (hL : 0<L) (Q a : ℕ) :
    cylinderFunctional L a (weightedRows amplitude Q)=(2/3 : ℝ)*
      ∑ q ∈ Finset.Icc 2 Q, if q∣L then amplitude q*primitiveValue q a else 0 := by
  simp only [weightedRows,map_smul,map_sum,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [cylinderFunctional_primitiveRow hL (by have := (Finset.mem_Icc.mp hq).1; omega)]
  split_ifs <;> simp

theorem cutoff_cylinder_agreement {L Q : ℕ} (hL : 0<L) (hLQ : L≤Q) (a : ℕ) :
    cylinderFunctional L a (weightedRows amplitude Q)=cylinderMean L a := by
  rw [cylinderFunctional_weightedRows hL,cylinderMean_conductors_ge_two hL]
  congr 1
  rw [← Finset.sum_filter,← Finset.sum_filter]
  have he : (Finset.Icc 2 Q).filter (fun q => q∣L)=L.divisors.filter (fun q => 2≤q) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · intro h; exact ⟨⟨h.2,hL.ne'⟩,h.1.1⟩
    · intro h; exact ⟨⟨h.2,(Nat.le_of_dvd hL h.1.1).trans hLQ⟩,h.1.1⟩
  rw [he]

theorem cutoff_residual_inner_residue {L Q : ℕ} (hL : 0<L) (hLQ : L≤Q) (a : ℕ) :
    inner ℝ (collisionPotential-weightedRows amplitude Q) (residueVector L a)=0 := by
  have hLR : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
  have he := cutoff_cylinder_agreement hL hLQ a
  rw [cylinderMean,cylinderFunctional_apply,cylinderFunctional_apply] at he
  have hi := mul_left_cancel₀ hLR he
  rw [real_inner_comm,inner_sub_right,hi]
  exact sub_self _

theorem residueMap_eq_value_indicator {L : ℕ} (hL : 0<L) {a : ℕ} (ha : a<L) (x : Phase) :
    letI : NeZero L := ⟨hL.ne'⟩
    residueMap L a x=if (residueHom L x).toAdd.val=a then 1 else 0 := by
  letI : NeZero L := ⟨hL.ne'⟩
  unfold residueMap
  rw [dif_pos hL]
  simp only [ContinuousMap.coe_mk]
  have he : (residueHom L x).toAdd=(a : ZMod L) ↔ (residueHom L x).toAdd.val=a := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha] using hv
    · intro h
      apply ZMod.val_injective
      simp only [ZMod.val_natCast,Nat.mod_eq_of_lt ha,h]
  simp only [he]

def residueTableMap (L : ℕ) (f : ℕ → ℝ) : C(Phase,ℝ) :=
  ∑ a ∈ Finset.range L, f a • residueMap L a

theorem residueTableMap_value {L : ℕ} (hL : 0<L) (f : ℕ → ℝ) (x : Phase) :
    letI : NeZero L := ⟨hL.ne'⟩
    residueTableMap L f x=f (residueHom L x).toAdd.val := by
  letI : NeZero L := ⟨hL.ne'⟩
  simp only [residueTableMap,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have he : (∑ a ∈ Finset.range L, f a*residueMap L a x)=
      ∑ a ∈ Finset.range L, if (residueHom L x).toAdd.val=a then f a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [residueMap_eq_value_indicator hL (Finset.mem_range.mp ha)]
    split_ifs <;> simp
  rw [he]
  simp [(residueHom L x).toAdd.val_lt]

theorem remainderMap_residue_expansion {L : ℕ} (hL : 0<L) :
    remainderMap L=residueTableMap L (centeredRemainder L) := by
  letI : NeZero L := ⟨hL.ne'⟩
  ext x
  rw [residueTableMap_value hL]
  simp only [remainderMap,ContinuousMap.coe_mk,centered_eq,centeredRemainder,
    Nat.mod_eq_of_lt (residueHom L x).toAdd.val_lt]

theorem remainderVector_residue_expansion {L : ℕ} (hL : 0<L) :
    remainderVector L=∑ a ∈ Finset.range L, centeredRemainder L a • residueVector L a := by
  rw [remainderVector,remainderMap_residue_expansion hL]
  simp only [residueTableMap,map_sum,map_smul,residueVector]

abbrev ConductorAddress (Q : ℕ) := Σ L : Fin (Q+1), Fin L.val

def conductorGenerator (Q : ℕ) (i : ConductorAddress Q) : HaarL2 :=
  residueVector i.1.val i.2.val

def conductorSpace (Q : ℕ) : Submodule ℝ HaarL2 :=
  Submodule.span ℝ (Set.range (conductorGenerator Q))

instance conductorSpace_finiteDimensional (Q : ℕ) : FiniteDimensional ℝ (conductorSpace Q) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem residueVector_mem_conductorSpace {L Q a : ℕ} (hLQ : L≤Q) (ha : a<L) :
    residueVector L a∈conductorSpace Q := by
  apply Submodule.subset_span
  exact ⟨⟨⟨L,by omega⟩,⟨a,ha⟩⟩,rfl⟩

theorem remainderVector_mem_conductorSpace {L Q : ℕ} (hL : 0<L) (hLQ : L≤Q) :
    remainderVector L∈conductorSpace Q := by
  rw [remainderVector_residue_expansion hL]
  apply Submodule.sum_mem
  intro a ha
  exact (conductorSpace Q).smul_mem _
    (residueVector_mem_conductorSpace hLQ (Finset.mem_range.mp ha))

theorem primitiveRow_mem_conductorSpace {q Q : ℕ} (hq : 0<q) (hqQ : q≤Q) :
    primitiveRow q∈conductorSpace Q := by
  unfold primitiveRow
  apply Submodule.sum_mem
  intro p hp
  have hd := Nat.snd_mem_divisors_of_mem_antidiagonal hp
  rw [← Int.cast_smul_eq_zsmul ℝ]
  exact (conductorSpace Q).smul_mem _
    (remainderVector_mem_conductorSpace (Nat.pos_of_mem_divisors hd)
      ((Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)).trans hqQ))

theorem weightedRows_mem_conductorSpace (Q : ℕ) : weightedRows amplitude Q∈conductorSpace Q := by
  unfold weightedRows
  apply (conductorSpace Q).smul_mem
  apply Submodule.sum_mem
  intro q hq
  exact (conductorSpace Q).smul_mem _ (primitiveRow_mem_conductorSpace
    (by have := (Finset.mem_Icc.mp hq).1; omega) (Finset.mem_Icc.mp hq).2)

theorem cutoff_residual_inner_conductorSpace (Q : ℕ) (v : HaarL2) (hv : v∈conductorSpace Q) :
    inner ℝ (collisionPotential-weightedRows amplitude Q) v=0 := by
  let ell : HaarL2 →L[ℝ] ℝ := innerSL ℝ (collisionPotential-weightedRows amplitude Q)
  have hk : conductorSpace Q≤ell.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change inner ℝ (collisionPotential-weightedRows amplitude Q)
      (residueVector i.1.val i.2.val)=0
    exact cutoff_residual_inner_residue (by have := i.2.isLt; omega)
      (by have := i.1.isLt; omega) i.2.val
  exact hk hv

theorem conductorSpace_projection (Q : ℕ) :
    (conductorSpace Q).starProjection collisionPotential=weightedRows amplitude Q :=
  (conductorSpace Q).eq_starProjection_of_mem_of_inner_eq_zero
    (weightedRows_mem_conductorSpace Q) (cutoff_residual_inner_conductorSpace Q)

theorem cutoff_pythagoras (Q : ℕ) :
    ‖collisionPotential-weightedRows amplitude Q‖^2+‖weightedRows amplitude Q‖^2=
      ‖collisionPotential‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (cutoff_residual_inner_conductorSpace Q _ (weightedRows_mem_conductorSpace Q))
  simpa only [sub_add_cancel,pow_two] using h.symm

theorem conductorEnergy_split (Q : ℕ) :
    (∑ q ∈ Finset.Icc 2 Q, jordanTwo q*(amplitude q)^2)+
      (∑' q : ℕ, if Q<q then conductorEnergy q else 0)=∑' q, conductorEnergy q := by
  have h := conductorEnergy_summable.sum_add_tsum_compl (s := Finset.Icc 2 Q)
  rw [tsum_subtype] at h
  convert! h using 1
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    simp only [conductorEnergy,if_pos (Finset.mem_Icc.mp hq).1]
  · apply tsum_congr
    intro q
    by_cases hq : 2≤q
    · simp [Set.indicator,hq,not_le]
    · simp [Set.indicator,conductorEnergy,hq]

theorem conductor_tail_summable (Q : ℕ) :
    Summable (fun q : ℕ => if Q<q then conductorEnergy q else 0) := by
  have h := conductorEnergy_summable.indicator {q | Q<q}
  change Summable (fun q => ({q | Q<q}.indicator conductorEnergy) q) at h
  simpa only [Set.indicator_apply,Set.mem_setOf_eq] using h

theorem conductor_projection_tail (Q : ℕ) :
    ‖collisionPotential-(conductorSpace Q).starProjection collisionPotential‖^2=
      (1/27 : ℝ)*∑' q : ℕ, if Q<q then conductorEnergy q else 0 := by
  rw [conductorSpace_projection]
  have h := cutoff_pythagoras Q
  rw [weightedRows_norm_sq,collisionPotential_variance] at h
  change ‖collisionPotential-weightedRows amplitude Q‖^2+
    (1/27 : ℝ)*(∑ q ∈ Finset.Icc 2 Q, jordanTwo q*(amplitude q)^2)=
    (1/27 : ℝ)*(∑' q, conductorEnergy q) at h
  rw [← conductorEnergy_split Q] at h
  linarith

theorem conductor_projection_tail_ge_one {Q : ℕ} (hQ : 1≤Q) :
    ‖collisionPotential-(conductorSpace Q).starProjection collisionPotential‖^2=
      (1/27 : ℝ)*∑' q : ℕ, if Q<q then jordanTwo q*(amplitude q)^2 else 0 := by
  rw [conductor_projection_tail]
  congr 1
  apply tsum_congr
  intro q
  by_cases hq : Q<q
  · simp only [if_pos hq,conductorEnergy,if_pos (by omega : 2≤q)]
  · simp only [if_neg hq]

theorem conductor_projection_converges :
    Tendsto (fun Q => (conductorSpace Q).starProjection collisionPotential)
      atTop (nhds collisionPotential) := by
  simpa only [conductorSpace_projection] using conductor_expansion_tendsto

theorem conductor_projection_tail_tendsto_zero :
    Tendsto (fun Q => ‖collisionPotential-
      (conductorSpace Q).starProjection collisionPotential‖^2) atTop (nhds 0) := by
  have h := ((tendsto_const_nhds (x := collisionPotential)).sub
    conductor_projection_converges).norm.pow 2
  simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using h

end NField.Alignment.CollisionConductorProjection
