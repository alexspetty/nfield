/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProfinitePeriodicTesting
import NField.Alignment.CollisionBoundaryMeasure
import Mathlib.Analysis.Normed.Group.Tannery

/-!+# Integer averages of the actual boundary increments

Positive-integer divisibility counts give a summable bound uniform in the
averaging length. This justifies passing from periodic reset terms to their
actual infinite series in the weak boundary pairing.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBoundaryTesting

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionResetIntegrability CollisionPotentialCoboundary CollisionPotentialHilbert
open CollisionPotentialConvergence ProfiniteOdometerErgodic ProfinitePeriodicTesting
open CollisionBoundaryMeasure

theorem resetTerm_locallyConstant (k : ℕ) : IsLocallyConstant (resetTerm k) := by
  by_cases hk : k=0
  · simp only [hk, resetTerm_zero]
    exact IsLocallyConstant.const 0
  have hkpos := Nat.pos_of_ne_zero hk
  letI : NeZero k := ⟨hk⟩
  let f : Multiplicative (ZMod k) → ℝ :=
    fun r => if r.toAdd=0 then (k : ℝ)*collisionWeight k else 0
  convert! (IsLocallyConstant.of_discrete f).comp_continuous (residueHom k).continuous_toFun using 1
  funext x
  simp [resetTerm, resetSet, hkpos, Set.indicator_apply, f]

def resetTest (k : ℕ) (φ : LocallyConstant Phase ℝ) : LocallyConstant Phase ℝ :=
  ⟨fun x => resetTerm k x*φ x, (resetTerm_locallyConstant k).mul φ.isLocallyConstant⟩

theorem resetTerm_integer (k n : ℕ) :
    resetTerm k (integerPhase n) = if k ∣ n then (k : ℝ)*collisionWeight k else 0 := by
  by_cases hk : k=0
  · simp [hk]
  have hkpos := Nat.pos_of_ne_zero hk
  letI : NeZero k := ⟨hk⟩
  unfold resetTerm
  rw [resetSet, dif_pos hkpos]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, residue_integer, Int.cast_natCast,
    ZMod.natCast_eq_zero_iff]

theorem positive_sum_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n+1))=∑ n ∈ Finset.Icc 1 N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1≤N+1), ih]

theorem resetTerm_positive_sum (k N : ℕ) :
    (∑ n ∈ Finset.range N, resetTerm k (integerPhase (n+1 : ℕ))) =
      (N/k : ℕ)*((k : ℝ)*collisionWeight k) := by
  simp_rw [resetTerm_integer]
  rw [positive_sum_Icc (fun n => if k ∣ n then (k : ℝ)*collisionWeight k else 0) N]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, multiples_Icc_card]

theorem resetTest_average_bound (k N : ℕ) (φ : LocallyConstant Phase ℝ) :
    ‖orbitAverage N (fun n => resetTest k φ (integerPhase n))‖ ≤
      ‖(φ : C(Phase, ℝ))‖*collisionWeight k := by
  by_cases hN : N=0
  · simp [hN, orbitAverage, mul_nonneg (norm_nonneg _) (collisionWeight_nonneg k)]
  have hNR : (0 : ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs : (∑ n ∈ Finset.range N, ‖resetTest k φ (integerPhase (n+1 : ℕ))‖) ≤
      ‖(φ : C(Phase, ℝ))‖*(∑ n ∈ Finset.range N, resetTerm k (integerPhase (n+1 : ℕ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    change ‖resetTerm k (integerPhase (n+1 : ℕ))*φ (integerPhase (n+1 : ℕ))‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (resetTerm_nonneg _ _)]
    convert! mul_le_mul_of_nonneg_left
      ((φ : C(Phase, ℝ)).norm_coe_le_norm _) (resetTerm_nonneg k (integerPhase (n+1 : ℕ)))
      using 1
    simp only [mul_comm]
  have hcount : ((N/k : ℕ) : ℝ)*(k : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N k
  calc
    _ ≤ (∑ n ∈ Finset.range N, ‖resetTest k φ (integerPhase (n+1 : ℕ))‖)/(N : ℝ) := by
      unfold orbitAverage
      rw [norm_div, Real.norm_eq_abs (N : ℝ), abs_of_pos hNR]
      exact div_le_div_of_nonneg_right (norm_sum_le _ _) hNR.le
    _ ≤ ‖(φ : C(Phase, ℝ))‖*((N/k : ℕ)*((k : ℝ)*collisionWeight k))/(N : ℝ) := by
      rw [← resetTerm_positive_sum]
      exact div_le_div_of_nonneg_right hs hNR.le
    _ ≤ _ := by
      apply (div_le_iff₀ hNR).mpr
      have h := mul_le_mul_of_nonneg_left hcount
        (mul_nonneg (norm_nonneg (φ : C(Phase, ℝ))) (collisionWeight_nonneg k))
      nlinarith

theorem resetTest_average_tendsto (k : ℕ) (φ : LocallyConstant Phase ℝ) :
    Tendsto (fun N => orbitAverage N (fun n => resetTest k φ (integerPhase n))) atTop
      (nhds (∫ x, resetTerm k x*φ x ∂phaseHaar)) :=
  locallyConstant_orbit_tendsto (resetTest k φ)

theorem resetTerm_trace_summable {n : ℕ} (hn : 0<n) :
    Summable (fun k => resetTerm k (integerPhase n)) := by
  convert! CollisionResolutionLaw.resetTerm_summable hn using 1
  funext k
  exact resetTerm_integer k n

theorem resetFunction_average_split (N : ℕ) (φ : LocallyConstant Phase ℝ) :
    orbitAverage N (fun n => resetFunction (integerPhase n)*φ (integerPhase n)) =
      ∑' k, orbitAverage N (fun n => resetTest k φ (integerPhase n)) := by
  unfold orbitAverage
  rw [tsum_div_const]
  congr 1
  have hs (n : ℕ) (_ : n ∈ Finset.range N) :
      Summable (fun k => resetTerm k (integerPhase (n+1 : ℕ))*φ (integerPhase (n+1 : ℕ))) :=
    (resetTerm_trace_summable (Nat.succ_pos n)).mul_right _
  change (∑ n ∈ Finset.range N, resetFunction (integerPhase (n+1 : ℕ))*φ (integerPhase (n+1 : ℕ))) =
    ∑' k, ∑ n ∈ Finset.range N, resetTerm k (integerPhase (n+1 : ℕ))*φ (integerPhase (n+1 : ℕ))
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (tsum_mul_right).symm

theorem resetTest_integrable (k : ℕ) (φ : LocallyConstant Phase ℝ) :
    Integrable (fun x => resetTerm k x*φ x) phaseHaar :=
  continuous_phase_integrable (resetTest k φ : C(Phase, ℝ))

theorem resetTest_integral_norm_bound (k : ℕ) (φ : LocallyConstant Phase ℝ) :
    (∫ x, ‖resetTerm k x*φ x‖ ∂phaseHaar) ≤ ‖(φ : C(Phase, ℝ))‖*collisionWeight k := by
  calc
    _ ≤ ∫ x, ‖(φ : C(Phase, ℝ))‖*resetTerm k x ∂phaseHaar := by
      apply integral_mono (resetTest_integrable k φ).norm
        ((resetTerm_integrable k).const_mul ‖(φ : C(Phase, ℝ))‖)
      intro x
      change ‖resetTerm k x*φ x‖ ≤ ‖(φ : C(Phase, ℝ))‖*resetTerm k x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (resetTerm_nonneg k x)]
      convert! mul_le_mul_of_nonneg_left ((φ : C(Phase, ℝ)).norm_coe_le_norm x)
        (resetTerm_nonneg k x) using 1
      simp only [mul_comm]
    _ = _ := by rw [integral_const_mul, integral_resetTerm]

theorem resetFunction_test_integrable (φ : LocallyConstant Phase ℝ) :
    Integrable (fun x => resetFunction x*φ x) phaseHaar :=
  resetFunction_integrable.mul_bdd φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (φ : C(Phase, ℝ)).norm_coe_le_norm)

theorem resetFunction_test_integral (φ : LocallyConstant Phase ℝ) :
    (∫ x, resetFunction x*φ x ∂phaseHaar) =
      ∑' k, ∫ x, resetTerm k x*φ x ∂phaseHaar := by
  have hs : Summable (fun k => ∫ x, ‖resetTerm k x*φ x‖ ∂phaseHaar) := by
    exact Summable.of_nonneg_of_le (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => resetTest_integral_norm_bound k φ)
      (collisionWeight_summable.mul_left ‖(φ : C(Phase, ℝ))‖)
  rw [integral_tsum_of_summable_integral_norm (fun k => resetTest_integrable k φ) hs]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (tsum_mul_right).symm)

theorem resetFunction_average_tendsto (φ : LocallyConstant Phase ℝ) :
    Tendsto (fun N => orbitAverage N
      (fun n => resetFunction (integerPhase n)*φ (integerPhase n))) atTop
      (nhds (∫ x, resetFunction x*φ x ∂phaseHaar)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (collisionWeight_summable.mul_left ‖(φ : C(Phase, ℝ))‖)
    (fun k => resetTest_average_tendsto k φ)
    (Eventually.of_forall (fun N k => resetTest_average_bound k N φ))
  simp only [resetFunction_average_split, resetFunction_test_integral]
  exact h

theorem increment_test_formula (φ : LocallyConstant Phase ℝ) (x : Phase) :
    increment x*φ x=(2/3 : ℝ)*(φ x-resetFunction x*φ x) := by
  unfold increment
  ring

theorem increment_test_integral (φ : LocallyConstant Phase ℝ) :
    (∫ x, increment x*φ x ∂phaseHaar) =
      (2/3 : ℝ)*((∫ x, φ x ∂phaseHaar)-(∫ x, resetFunction x*φ x ∂phaseHaar)) := by
  simp_rw [increment_test_formula]
  rw [integral_const_mul]
  congr 1
  convert! integral_sub (continuous_phase_integrable (φ : C(Phase, ℝ)))
    (resetFunction_test_integrable φ) using 1

theorem increment_test_average (φ : LocallyConstant Phase ℝ) (N : ℕ) :
    orbitAverage N (fun n => increment (integerPhase n)*φ (integerPhase n)) =
      (2/3 : ℝ)*(orbitAverage N (fun n => φ (integerPhase n))-
        orbitAverage N (fun n => resetFunction (integerPhase n)*φ (integerPhase n))) := by
  unfold orbitAverage
  simp_rw [increment_test_formula]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

theorem increment_test_tendsto (φ : LocallyConstant Phase ℝ) :
    Tendsto (fun N => orbitAverage N (fun n => increment (integerPhase n)*φ (integerPhase n)))
      atTop (nhds (∫ x, increment x*φ x ∂phaseHaar)) := by
  simp only [increment_test_average, increment_test_integral]
  exact ((locallyConstant_orbit_tendsto φ).sub (resetFunction_average_tendsto φ)).const_mul _

/-- The boundary readout uses the actual squared continuous response. -/
def boundaryIncrement (n : ℕ) : ℝ :=
  1-(∫ t in (0 : ℝ)..1, CollisionRampEnergy.boundaryResponse n t^2)+
    (∫ t in (0 : ℝ)..1, CollisionRampEnergy.boundaryResponse (n-1) t^2)

theorem boundaryIncrement_succ (N : ℕ) :
    boundaryIncrement (N+1)=deficit (N+1)-deficit N := by
  unfold boundaryIncrement
  simp only [Nat.add_sub_cancel, CollisionRampEnergy.boundaryResponse_energy,
    deficit_eq_capacity, Nat.cast_add, Nat.cast_one]
  ring

theorem resetFunction_integer {n : ℕ} (hn : 0<n) :
    resetFunction (integerPhase n) = ∑ k ∈ n.divisors, (k : ℝ)*collisionWeight k := by
  have he : (fun k => resetTerm k (integerPhase n))=CollisionResolutionLaw.resetTerm n := by
    funext k
    exact resetTerm_integer k n
  rw [resetFunction, he, CollisionResolutionLaw.resetTerm_tsum hn]

theorem boundaryIncrement_integer {n : ℕ} (hn : 0<n) :
    boundaryIncrement n=increment (integerPhase n) := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [boundaryIncrement_succ, CollisionResolutionLaw.deficit_reset, increment,
    resetFunction_integer (Nat.succ_pos N)]

theorem boundary_increment_average_tendsto (φ : LocallyConstant Phase ℝ) :
    Tendsto (fun N => orbitAverage N (fun n => boundaryIncrement n*φ (integerPhase n)))
      atTop (nhds (∫ x, increment x*φ x ∂phaseHaar)) := by
  have he (N : ℕ) : orbitAverage N (fun n => boundaryIncrement n*φ (integerPhase n)) =
      orbitAverage N (fun n => increment (integerPhase n)*φ (integerPhase n)) := by
    unfold orbitAverage
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    change boundaryIncrement (n+1)*φ (integerPhase (n+1 : ℕ)) =
      increment (integerPhase (n+1 : ℕ))*φ (integerPhase (n+1 : ℕ))
    rw [boundaryIncrement_integer (Nat.succ_pos n)]
  simpa only [he] using increment_test_tendsto φ

def HasRealBoundaryPairings (F : HaarL2) : Prop :=
  ∀ φ : LocallyConstant Phase ℝ,
    Tendsto (fun N => orbitAverage N (fun n => boundaryIncrement n*φ (integerPhase n))) atTop
      (nhds (∫ x, (F x-F (CollisionPotentialCoboundary.translate (-1) x))*φ x ∂phaseHaar))

theorem collisionPotential_real_boundary_pairings : HasRealBoundaryPairings collisionPotential := by
  intro φ
  have he : (∫ x, increment x*φ x ∂phaseHaar) =
      ∫ x, (collisionPotential x-collisionPotential (CollisionPotentialCoboundary.translate (-1) x))*φ x ∂phaseHaar := by
    apply integral_congr_ae
    filter_upwards [increment_coboundary_ae] with x hx
    rw [hx]
  rw [← he]
  exact boundary_increment_average_tendsto φ

theorem difference_test_coe (F : HaarL2) (φ : LocallyConstant Phase ℝ) :
    (∫ x, (F-shift (-1) F) x*φ x ∂phaseHaar) =
      ∫ x, (F x-F (CollisionPotentialCoboundary.translate (-1) x))*φ x ∂phaseHaar := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub F (shift (-1) F), shift_coe (-1) F] with x hsub hshift
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hshift]

theorem real_boundary_pairings_unique (F G : HaarL2)
    (hF : HasRealBoundaryPairings F) (hG : HasRealBoundaryPairings G)
    (hmF : (∫ x, F x ∂phaseHaar)=0) (hmG : (∫ x, G x ∂phaseHaar)=0) : F=G := by
  apply mean_zero_coboundary_unique F G hmF hmG
  apply locallyConstant_L2_separates
  intro φ
  rw [difference_test_coe, difference_test_coe]
  exact tendsto_nhds_unique (hF φ) (hG φ)

theorem difference_test_integrable (F : HaarL2) (φ : LocallyConstant Phase ℝ) :
    Integrable (fun x => (F x-F (CollisionPotentialCoboundary.translate (-1) x))*φ x) phaseHaar := by
  have hi := CollisionL1Testing.continuous_test_integrable (φ : C(Phase, ℝ))
    (CollisionL1Testing.lowerL2 (F-shift (-1) F))
  apply hi.congr
  filter_upwards [Lp.coeFn_sub F (shift (-1) F), shift_coe (-1) F] with x hsub hshift
  simp only [CollisionL1Testing.lowerL2_coe, Pi.sub_apply] at *
  rw [hsub, hshift]
  rfl

def realPartTest (φ : LocallyConstant Phase ℂ) : LocallyConstant Phase ℝ := φ.map Complex.re
def imagPartTest (φ : LocallyConstant Phase ℂ) : LocallyConstant Phase ℝ := φ.map Complex.im

theorem real_conjugate_product (u : ℝ) (z : ℂ) :
    (u : ℂ)*star z=(u*z.re : ℝ)-(u*z.im : ℝ)*Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

def complexOrbitAverage (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, f (n+1))/(N : ℂ)

theorem complex_test_average_split (u : ℕ → ℝ) (φ : LocallyConstant Phase ℂ) (N : ℕ) :
    complexOrbitAverage N (fun n => (u n : ℂ)*star (φ (integerPhase n))) =
      (orbitAverage N (fun n => u n*realPartTest φ (integerPhase n)) : ℂ)-
        (orbitAverage N (fun n => u n*imagPartTest φ (integerPhase n)) : ℂ)*Complex.I := by
  unfold complexOrbitAverage orbitAverage
  simp only [real_conjugate_product, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast,
    realPartTest, imagPartTest, LocallyConstant.map_apply, Function.comp_def]
  ring

theorem complex_test_integral_split (F : HaarL2) (φ : LocallyConstant Phase ℂ) :
    (∫ x, ((F x-F (CollisionPotentialCoboundary.translate (-1) x)) : ℂ)*star (φ x) ∂phaseHaar) =
      ((∫ x, (F x-F (CollisionPotentialCoboundary.translate (-1) x))*realPartTest φ x ∂phaseHaar : ℝ) : ℂ)-
        ((∫ x, (F x-F (CollisionPotentialCoboundary.translate (-1) x))*imagPartTest φ x ∂phaseHaar : ℝ) : ℂ)*Complex.I := by
  have hR : Integrable (fun x => (((F x-F (CollisionPotentialCoboundary.translate (-1) x))*realPartTest φ x : ℝ) : ℂ)) phaseHaar :=
    (difference_test_integrable F (realPartTest φ)).ofReal
  have hI : Integrable (fun x => (((F x-F (CollisionPotentialCoboundary.translate (-1) x))*imagPartTest φ x : ℝ) : ℂ)) phaseHaar :=
    (difference_test_integrable F (imagPartTest φ)).ofReal
  have he : (fun x => ((F x-F (CollisionPotentialCoboundary.translate (-1) x)) : ℂ)*star (φ x)) =
      fun x => (((F x-F (CollisionPotentialCoboundary.translate (-1) x))*realPartTest φ x : ℝ) : ℂ)-
        (((F x-F (CollisionPotentialCoboundary.translate (-1) x))*imagPartTest φ x : ℝ) : ℂ)*Complex.I := by
    funext x
    simpa only [Complex.ofReal_sub, realPartTest, imagPartTest,
      LocallyConstant.map_apply, Function.comp_def] using
      real_conjugate_product (F x-F (CollisionPotentialCoboundary.translate (-1) x)) (φ x)
  rw [he, integral_sub hR (hI.mul_const Complex.I), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]

def HasBoundaryPairings (F : HaarL2) : Prop :=
  ∀ φ : LocallyConstant Phase ℂ,
    Tendsto (fun N => complexOrbitAverage N
      (fun n => (boundaryIncrement n : ℂ)*star (φ (integerPhase n)))) atTop
      (nhds (∫ x, ((F x-F (CollisionPotentialCoboundary.translate (-1) x)) : ℂ)*star (φ x) ∂phaseHaar))

theorem real_boundary_pairings_complex (F : HaarL2) (hF : HasRealBoundaryPairings F) :
    HasBoundaryPairings F := by
  intro φ
  simp only [complex_test_average_split, complex_test_integral_split]
  have hR := (Complex.continuous_ofReal.tendsto _).comp (hF (realPartTest φ))
  have hI := (Complex.continuous_ofReal.tendsto _).comp (hF (imagPartTest φ))
  exact hR.sub (hI.mul_const Complex.I)

theorem complex_boundary_pairings_real (F : HaarL2) (hF : HasBoundaryPairings F) :
    HasRealBoundaryPairings F := by
  intro φ
  let ψ : LocallyConstant Phase ℂ := φ.map Complex.ofReal
  have h := hF ψ
  simp only [complex_test_average_split, complex_test_integral_split] at h
  have hr := (Complex.continuous_re.tendsto _).comp h
  simpa [realPartTest, imagPartTest, ψ, LocallyConstant.map_apply,
    Function.comp_def, orbitAverage] using hr

theorem boundary_pairings_iff_real (F : HaarL2) :
    HasBoundaryPairings F ↔ HasRealBoundaryPairings F :=
  ⟨complex_boundary_pairings_real F, real_boundary_pairings_complex F⟩

theorem collisionPotential_boundary_pairings : HasBoundaryPairings collisionPotential :=
  real_boundary_pairings_complex collisionPotential collisionPotential_real_boundary_pairings

theorem boundary_weak_pairing (φ : LocallyConstant Phase ℂ) :
    Tendsto (fun N => complexOrbitAverage N
      (fun n => (boundaryIncrement n : ℂ)*star (φ (integerPhase n)))) atTop
      (nhds (∫ x, ((collisionPotential x-
        collisionPotential (CollisionPotentialCoboundary.translate (-1) x)) : ℂ)*star (φ x) ∂phaseHaar)) :=
  collisionPotential_boundary_pairings φ

theorem intrinsic_boundary_potential :
    (∫ x, collisionPotential x ∂phaseHaar)=0 ∧ HasBoundaryPairings collisionPotential ∧
      ∀ F : HaarL2, (∫ x, F x ∂phaseHaar)=0 → HasBoundaryPairings F → F=collisionPotential := by
  refine ⟨collisionPotential_mean_zero, collisionPotential_boundary_pairings, ?_⟩
  intro F hm hF
  exact real_boundary_pairings_unique F collisionPotential
    (complex_boundary_pairings_real F hF) collisionPotential_real_boundary_pairings
    hm collisionPotential_mean_zero

theorem boundary_potential_exists_unique :
    ∃! F : HaarL2, (∫ x, F x ∂phaseHaar)=0 ∧ HasBoundaryPairings F := by
  refine ⟨collisionPotential,
    ⟨intrinsic_boundary_potential.1, intrinsic_boundary_potential.2.1⟩, ?_⟩
  intro F hF
  exact intrinsic_boundary_potential.2.2 F hF.1 hF.2

end NField.Alignment.CollisionBoundaryTesting
