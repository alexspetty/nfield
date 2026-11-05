/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorProjection
import NField.Alignment.CollisionPotentialCutoff
import NField.Alignment.CollisionCylinderOne

/-!
# Finite Haar cylinder projection and its dyadic approximation rate

The actual conditional residue means form the orthogonal projection onto
the entire finite residue quotient. Best approximation transfers the sharp
potential cutoff bound to these cylinder means.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCylinderProjection

open scoped BigOperators Classical
open Filter ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCutoff CollisionCylinderMeans
open CollisionConductorProjection CollisionOdometerRecurrence CollisionCylinderOne

def cylinderSpace (L : ℕ) : Submodule ℝ HaarL2 :=
  Submodule.span ℝ (Set.range (fun a : Fin L => residueVector L a.val))

instance cylinderSpace_finiteDimensional (L : ℕ) : FiniteDimensional ℝ (cylinderSpace L) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

def residueProjection (L : ℕ) (Y : HaarL2) : HaarL2 :=
  ∑ a ∈ Finset.range L, cylinderFunctional L a Y • residueVector L a

def cylinderApproximation (L : ℕ) : HaarL2 := residueProjection L collisionPotential

theorem residueVector_mem_cylinderSpace {L a : ℕ} (ha : a < L) :
    residueVector L a ∈ cylinderSpace L :=
  Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩

theorem residueProjection_mem (L : ℕ) (Y : HaarL2) : residueProjection L Y ∈ cylinderSpace L := by
  apply Submodule.sum_mem
  intro a ha
  exact (cylinderSpace L).smul_mem _ (residueVector_mem_cylinderSpace (Finset.mem_range.mp ha))

theorem same_cylinder_gram {L a b : ℕ} (hL : 0 < L) (ha : a < L) (hb : b < L) :
    inner ℝ (residueVector L a) (residueVector L b)=if a=b then 1/(L : ℝ) else 0 := by
  rw [residueVector_pair_inner hL hL,Nat.gcd_self,Nat.lcm_self]
  simp only [Nat.ModEq,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

theorem residueProjection_inner {L a : ℕ} (hL : 0 < L) (ha : a < L) (Y : HaarL2) :
    inner ℝ (residueVector L a) (residueProjection L Y)=inner ℝ (residueVector L a) Y := by
  rw [residueProjection,inner_sum]
  have he (b : ℕ) (hb : b ∈ Finset.range L) :
      inner ℝ (residueVector L a) (cylinderFunctional L b Y • residueVector L b)=
        if a=b then cylinderFunctional L a Y/(L : ℝ) else 0 := by
    rw [inner_smul_right,same_cylinder_gram hL ha (Finset.mem_range.mp hb)]
    split_ifs with h
    · subst b
      ring
    · simp only [mul_zero]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_ite_eq,Finset.mem_range,ha,if_true,cylinderFunctional_apply]
  have hLR : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
  field_simp

theorem residueProjection_residual_inner {L : ℕ} (hL : 0 < L) (Y v : HaarL2)
    (hv : v ∈ cylinderSpace L) : inner ℝ (Y-residueProjection L Y) v=0 := by
  let ell : HaarL2 →L[ℝ] ℝ := innerSL ℝ (Y-residueProjection L Y)
  have hk : cylinderSpace L ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change inner ℝ (Y-residueProjection L Y) (residueVector L a.val)=0
    rw [real_inner_comm,inner_sub_right,residueProjection_inner hL a.isLt]
    exact sub_self _
  exact hk hv

theorem residueProjection_eq_starProjection {L : ℕ} (hL : 0 < L) (Y : HaarL2) :
    (cylinderSpace L).starProjection Y=residueProjection L Y :=
  (cylinderSpace L).eq_starProjection_of_mem_of_inner_eq_zero
    (residueProjection_mem L Y) (residueProjection_residual_inner hL Y)

theorem cylinderApproximation_table (L : ℕ) :
    cylinderApproximation L=
      ContinuousMap.toLp 2 phaseHaar ℝ (residueTableMap L (cylinderMean L)) := by
  simp only [cylinderApproximation,residueProjection,residueTableMap,map_sum,map_smul,
    residueVector,cylinderMean]

theorem remainderMap_on_cylinder {k L : ℕ} (hk : 0 < k) (hL : 0 < L) (hkL : k ∣ L) :
    remainderMap k=residueTableMap L (centeredRemainder k) := by
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero L := ⟨hL.ne'⟩
  ext x
  rw [residueTableMap_value hL]
  exact centered_via_residue hkL x

theorem remainderVector_mem_cylinderSpace {k L : ℕ} (hk : 0 < k) (hL : 0 < L) (hkL : k ∣ L) :
    remainderVector k ∈ cylinderSpace L := by
  rw [remainderVector,remainderMap_on_cylinder hk hL hkL]
  simp only [residueTableMap,map_sum,map_smul]
  apply Submodule.sum_mem
  intro a ha
  exact (cylinderSpace L).smul_mem _ (residueVector_mem_cylinderSpace (Finset.mem_range.mp ha))

theorem finitePotential_mem_cutoffCylinder (M : ℕ) :
    finitePotential collisionWeight M ∈ cylinderSpace (cutoffPeriod M) := by
  unfold finitePotential
  apply (cylinderSpace (cutoffPeriod M)).smul_mem
  apply Submodule.sum_mem
  intro k hk
  apply (cylinderSpace (cutoffPeriod M)).smul_mem
  exact remainderVector_mem_cylinderSpace (by have := (Finset.mem_Icc.mp hk).1; omega)
    (cutoffPeriod_pos M) (dvd_cutoffPeriod (by have := (Finset.mem_Icc.mp hk).1; omega)
      (Finset.mem_Icc.mp hk).2)

theorem cylinderProjection_best {L : ℕ} (hL : 0 < L) (Y v : HaarL2) (hv : v ∈ cylinderSpace L) :
    ‖Y-residueProjection L Y‖ ≤ ‖Y-v‖ := by
  rw [← residueProjection_eq_starProjection hL,Submodule.starProjection_minimal]
  exact ciInf_le ⟨0,Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨v,hv⟩ : cylinderSpace L)

theorem cylinder_cutoff_error_le (M : ℕ) :
    ‖collisionPotential-cylinderApproximation (cutoffPeriod M)‖ ≤
      ‖collisionPotential-finitePotential collisionWeight M‖ :=
  cylinderProjection_best (cutoffPeriod_pos M) _ _ (finitePotential_mem_cutoffCylinder M)

theorem cylinder_cutoff_error_bound {M : ℕ} (hM : 1 ≤ M) :
    ‖collisionPotential-cylinderApproximation (cutoffPeriod M)‖ ≤
      cutoffConstant*(1+Real.log (2*(M : ℝ)))/Real.sqrt (M : ℝ) :=
  (cylinder_cutoff_error_le M).trans (collisionPotential_cutoff_bound hM)

theorem dyadic_inverse_sqrt (j : ℕ) :
    1/Real.sqrt ((2^j : ℕ) : ℝ)=(2 : ℝ)^(-(j : ℝ)/2) := by
  rw [Nat.cast_pow,Nat.cast_two,Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),one_div,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem dyadic_log_factor_bound {j : ℕ} (hj : 1 ≤ j) :
    1+Real.log (2*((2^j : ℕ) : ℝ)) ≤ (1+2*Real.log 2)*(j : ℝ) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [Nat.cast_pow,Nat.cast_two,Real.log_mul (by norm_num : (2 : ℝ)≠0)
    (pow_ne_zero _ (by norm_num : (2 : ℝ)≠0)),Real.log_pow]
  nlinarith

theorem dyadic_cylinder_error_bound {j : ℕ} (hj : 1 ≤ j) :
    ‖collisionPotential-cylinderApproximation (cutoffPeriod (2^j))‖ ≤
      (cutoffConstant*(1+2*Real.log 2))*((j : ℝ)*(2 : ℝ)^(-(j : ℝ)/2)) := by
  have h := cylinder_cutoff_error_bound (M := 2^j) (Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2))
  have hfactor := mul_le_mul_of_nonneg_left (dyadic_log_factor_bound hj) cutoffConstant_nonneg
  have hdiv := div_le_div_of_nonneg_right hfactor (Real.sqrt_nonneg ((2^j : ℕ) : ℝ))
  calc
    ‖collisionPotential-cylinderApproximation (cutoffPeriod (2^j))‖ ≤
        cutoffConstant*(1+Real.log (2*((2^j : ℕ) : ℝ)))/Real.sqrt ((2^j : ℕ) : ℝ) := h
    _ ≤ cutoffConstant*((1+2*Real.log 2)*(j : ℝ))/Real.sqrt ((2^j : ℕ) : ℝ) := hdiv
    _ = _ := by
      rw [div_eq_mul_one_div,dyadic_inverse_sqrt]
      ring

theorem dyadic_cylinder_approximation :
    Asymptotics.IsBigO atTop
      (fun j : ℕ => collisionPotential-cylinderApproximation (cutoffPeriod (2^j)))
      (fun j : ℕ => (j : ℝ)*(2 : ℝ)^(-(j : ℝ)/2)) := by
  apply Asymptotics.IsBigO.of_bound (cutoffConstant*(1+2*Real.log 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)*(2 : ℝ)^(-(j : ℝ)/2))]
  exact dyadic_cylinder_error_bound hj

end NField.Alignment.CollisionCylinderProjection
