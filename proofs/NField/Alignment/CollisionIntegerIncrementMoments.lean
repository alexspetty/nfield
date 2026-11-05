/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerJointMoments

/-!
# Empirical moments of the literal increments and deficit blocks

Finite polynomial expansion transfers the positive reset-product limits to
the signed increments. All shifts and block lengths remain fixed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerIncrementMoments

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure ProfinitePeriodicTesting CollisionRemainderDynamics
open CollisionMassReadout CollisionBoundaryTesting CollisionPotentialCoboundary
open CollisionResetIntegrability CollisionJointMoments CollisionIntegerJointMoments

theorem reset_product_integrable {ι : Type*} [Fintype ι] (h : ι → ℕ) :
    Integrable (fun x => ∏ i, resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x)) phaseHaar := by
  let e := (Fintype.equivFin ι).symm
  have hi := reset_joint_integrable (Fintype.card ι) (fun i => h (e i))
  convert! hi using 1
  funext x
  exact (e.prod_comp (fun i => resetFunction
    (CollisionPotentialCoboundary.translate (h i : ℤ) x))).symm

theorem reset_product_tendsto {ι : Type*} [Fintype ι] (h : ι → ℕ) :
    Tendsto (fun N => orbitAverage N
      (fun n => ∏ i, resetFunction (integerPhase (n+h i : ℕ)))) atTop
      (nhds (∫ x, ∏ i, resetFunction
        (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar)) := by
  let e := (Fintype.equivFin ι).symm
  have ht := reset_joint_moment_tendsto (Fintype.card ι) (fun i => h (e i))
  convert! ht using 1
  · funext N
    congr 1
    funext n
    exact (e.prod_comp (fun i => resetFunction (integerPhase (n+h i : ℕ)))).symm
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (e.prod_comp (fun i => resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x))).symm)

theorem reset_subproduct_integrable {ι : Type*} (S : Finset ι) (h : ι → ℕ) :
    Integrable (fun x => ∏ i ∈ S, resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x)) phaseHaar := by
  have hi := reset_product_integrable (fun i : S => h i)
  convert! hi using 1
  funext x
  exact (Finset.prod_coe_sort S (fun i => resetFunction
    (CollisionPotentialCoboundary.translate (h i : ℤ) x))).symm

theorem reset_subproduct_tendsto {ι : Type*} (S : Finset ι) (h : ι → ℕ) :
    Tendsto (fun N => orbitAverage N
      (fun n => ∏ i ∈ S, resetFunction (integerPhase (n+h i : ℕ)))) atTop
      (nhds (∫ x, ∏ i ∈ S, resetFunction
        (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar)) := by
  have ht := reset_product_tendsto (fun i : S => h i)
  convert! ht using 1
  · funext N
    congr 1
    funext n
    exact (Finset.prod_coe_sort S (fun i => resetFunction (integerPhase (n+h i : ℕ)))).symm
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (Finset.prod_coe_sort S (fun i => resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x))).symm)

theorem increment_product_expansion {ι : Type*} [Fintype ι] (x : ι → Phase) :
    (∏ i, increment (x i)) = (2/3 : ℝ)^(Fintype.card ι)*
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℝ)^S.card*∏ i ∈ S, resetFunction (x i) := by
  unfold increment
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]

theorem increment_product_integrable {ι : Type*} [Fintype ι] (h : ι → ℕ) :
    Integrable (fun x => ∏ i, increment
      (CollisionPotentialCoboundary.translate (h i : ℤ) x)) phaseHaar := by
  simp_rw [increment_product_expansion]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro S _
  exact (reset_subproduct_integrable S h).const_mul _

theorem increment_product_integral {ι : Type*} [Fintype ι] (h : ι → ℕ) :
    (∫ x, ∏ i, increment (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) =
      (2/3 : ℝ)^(Fintype.card ι)*∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℝ)^S.card*(∫ x, ∏ i ∈ S, resetFunction
          (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) := by
  simp_rw [increment_product_expansion]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro S _
    exact (reset_subproduct_integrable S h).const_mul _

theorem increment_product_average {ι : Type*} [Fintype ι] (N : ℕ) (h : ι → ℕ) :
    orbitAverage N (fun n => ∏ i, increment (integerPhase (n+h i : ℕ))) =
      (2/3 : ℝ)^(Fintype.card ι)*∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℝ)^S.card*orbitAverage N
          (fun n => ∏ i ∈ S, resetFunction (integerPhase (n+h i : ℕ))) := by
  unfold orbitAverage
  simp_rw [increment_product_expansion]
  rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.mul_sum, mul_div_assoc]

theorem increment_product_tendsto {ι : Type*} [Fintype ι] (h : ι → ℕ) :
    Tendsto (fun N => orbitAverage N
      (fun n => ∏ i, increment (integerPhase (n+h i : ℕ)))) atTop
      (nhds (∫ x, ∏ i, increment
        (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar)) := by
  simp only [increment_product_average, increment_product_integral]
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro S _
  exact (reset_subproduct_tendsto S h).const_mul _

theorem increment_mixed_moment_tendsto (r : ℕ) (h p : Fin r → ℕ) :
    Tendsto (fun N => orbitAverage N
      (fun n => ∏ i, increment (integerPhase (n+h i : ℕ))^(p i))) atTop
      (nhds (∫ x, ∏ i, increment
        (CollisionPotentialCoboundary.translate (h i : ℤ) x)^(p i) ∂phaseHaar)) := by
  have ht := increment_product_tendsto (fun j : (Σ i : Fin r, Fin (p i)) => h j.1)
  simpa only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using ht

theorem increment_pair_integrable (a b : ℕ) :
    Integrable (fun x => increment (CollisionPotentialCoboundary.translate (a : ℤ) x)*
      increment (CollisionPotentialCoboundary.translate (b : ℤ) x)) phaseHaar := by
  simpa using increment_product_integrable ![a,b]

theorem increment_pair_tendsto (a b : ℕ) :
    Tendsto (fun N => orbitAverage N (fun n =>
      increment (integerPhase (n+a : ℕ))*increment (integerPhase (n+b : ℕ)))) atTop
      (nhds (∫ x, increment (CollisionPotentialCoboundary.translate (a : ℤ) x)*
        increment (CollisionPotentialCoboundary.translate (b : ℤ) x) ∂phaseHaar)) := by
  simpa using increment_product_tendsto ![a,b]

theorem deficit_block_integer (n H : ℕ) :
    deficit (n+H)-deficit n=blockFunction H (integerPhase n) := by
  rw [blockFunction, ← positive_sum_Icc]
  simp_rw [translate_integerPhase]
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hs := (boundaryIncrement_integer (Nat.succ_pos (n+H))).symm.trans
      (boundaryIncrement_succ (n+H))
    rw [show n+(H+1)=n+H+1 by omega, hs]
    ring

theorem block_square_expansion (H : ℕ) (x : Phase) :
    |blockFunction H x|^2 = ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
      increment (CollisionPotentialCoboundary.translate (a : ℤ) x)*
        increment (CollisionPotentialCoboundary.translate (b : ℤ) x) := by
  rw [sq_abs, pow_two, blockFunction, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem block_square_integral (H : ℕ) :
    (∫ x, |blockFunction H x|^2 ∂phaseHaar) =
      ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
        ∫ x, increment (CollisionPotentialCoboundary.translate (a : ℤ) x)*
          increment (CollisionPotentialCoboundary.translate (b : ℤ) x) ∂phaseHaar := by
  simp_rw [block_square_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    exact integral_finsetSum _ (fun b _ => increment_pair_integrable a b)
  · intro a _
    exact integrable_finsetSum _ (fun b _ => increment_pair_integrable a b)

theorem deficit_block_square_average (N H : ℕ) :
    orbitAverage N (fun n => |deficit (n+H)-deficit n|^2) =
      ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
        orbitAverage N (fun n => increment (integerPhase (n+a : ℕ))*
          increment (integerPhase (n+b : ℕ))) := by
  simp_rw [deficit_block_integer, block_square_expansion, translate_integerPhase]
  unfold orbitAverage
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range N), Finset.sum_div]

theorem deficit_block_second_moment_tendsto (H : ℕ) :
    Tendsto (fun N => orbitAverage N (fun n => |deficit (n+H)-deficit n|^2)) atTop
      (nhds (∫ x, |blockFunction H x|^2 ∂phaseHaar)) := by
  simp only [deficit_block_square_average, block_square_integral]
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  exact increment_pair_tendsto a b

end NField.Alignment.CollisionIntegerIncrementMoments
