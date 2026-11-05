/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerJointMoments
import NField.Alignment.CollisionAmplitudeEnclosure

/-!
# Uniform L1 approximation for empirical increment laws

Integer trace tails and Haar tails are established independently. These
estimates will be used with bounded Lipschitz tests on finite vectors.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerLawApproximation

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure ProfinitePeriodicTesting CollisionRemainderDynamics
open CollisionMassReadout CollisionBoundaryTesting CollisionPotentialCoboundary
open CollisionResetIntegrability CollisionJointMoments CollisionIntegerJointMoments
open CollisionIntegerSingularity CollisionAmplitudeEnclosure

def resetPartial (M : ℕ) (x : Phase) : ℝ := ∑ k ∈ Finset.range (M+1), resetTerm k x

theorem locallyConstant_finsetSum {ι : Type*} (S : Finset ι) (f : ι → Phase → ℝ)
    (hf : ∀ i ∈ S, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∑ i ∈ S, f i x) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    convert! (IsLocallyConstant.const (0 : ℝ)) using 1
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem resetPartial_locallyConstant (M : ℕ) : IsLocallyConstant (resetPartial M) :=
  locallyConstant_finsetSum _ _ (fun k _ => resetTerm_locallyConstant k)

theorem resetPartial_integrable (M : ℕ) : Integrable (resetPartial M) phaseHaar :=
  integrable_finsetSum _ (fun k _ => resetTerm_integrable k)

theorem resetPartial_integral (M : ℕ) :
    (∫ x, resetPartial M x ∂phaseHaar)=∑ k ∈ Finset.Icc 2 M, collisionWeight k := by
  unfold resetPartial
  rw [integral_finsetSum _ (fun k _ => resetTerm_integrable k)]
  simp only [integral_resetTerm, sum_range_weights]

theorem resetPartial_le_of_summable (M : ℕ) {x : Phase}
    (hx : Summable (fun k => resetTerm k x)) : resetPartial M x≤resetFunction x := by
  exact hx.sum_le_tsum _ (fun k _ => resetTerm_nonneg k x)

theorem resetPartial_L1_error (M : ℕ) :
    (∫ x, ‖resetFunction x-resetPartial M x‖ ∂phaseHaar)=tailMass M := by
  have he : (fun x => ‖resetFunction x-resetPartial M x‖) =ᵐ[phaseHaar]
      (fun x => resetFunction x-resetPartial M x) := by
    filter_upwards [resetTerm_summable_ae] with x hx
    exact Real.norm_of_nonneg (sub_nonneg.mpr (resetPartial_le_of_summable M hx))
  rw [integral_congr_ae he, integral_sub resetFunction_integrable (resetPartial_integrable M),
    resetFunction_mean, resetPartial_integral, tailMass_eq_complement]

theorem resetPartial_shifted_L1_error (M h : ℕ) :
    (∫ x, ‖resetFunction (CollisionPotentialCoboundary.translate (h : ℤ) x)-
      resetPartial M (CollisionPotentialCoboundary.translate (h : ℤ) x)‖ ∂phaseHaar)=tailMass M := by
  have he := (translate_measurePreserving (h : ℤ)).integral_comp
    (MeasurableEquiv.mulLeft (integerPhase (h : ℤ))).measurableEmbedding
    (fun x => ‖resetFunction x-resetPartial M x‖)
  exact he.trans (resetPartial_L1_error M)

def resetShiftTrace (k h N : ℕ) : ℝ :=
  orbitAverage N (fun n => resetTerm k (integerPhase (n+h : ℕ)))

theorem resetShiftTrace_nonneg (k h N : ℕ) : 0≤resetShiftTrace k h N :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => resetTerm_nonneg _ _)) (Nat.cast_nonneg N)

theorem resetShiftTrace_eq_count (k h N : ℕ) : resetShiftTrace k h N =
    ((k : ℝ)*collisionWeight k)*
      ((∑ n ∈ Finset.range N, divisorIndicator k (n+1+h))/(N : ℝ)) := by
  unfold resetShiftTrace orbitAverage divisorIndicator
  simp_rw [resetTerm_integer]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem resetShiftTrace_bound (k h N : ℕ) :
    resetShiftTrace k h N≤(1+(h : ℝ))*collisionWeight k := by
  by_cases hk : k=0
  · subst k
    simp [resetShiftTrace, orbitAverage]
  by_cases hN : N=0
  · subst N
    simpa [resetShiftTrace, orbitAverage] using
      mul_nonneg (by positivity : 0≤1+(h : ℝ)) (collisionWeight_nonneg k)
  have hkR : (0 : ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hf : ((∑ n ∈ Finset.range N, divisorIndicator k (n+1+h))/(N : ℝ))≤
      (1+(h : ℝ))/(k : ℝ) :=
    (div_le_div_of_nonneg_right (shifted_divisor_count_bound k N h)
      (Nat.cast_nonneg N)).trans
      (nat_div_average_bound k N h (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hN))
  rw [resetShiftTrace_eq_count]
  calc
    _ ≤ ((k : ℝ)*collisionWeight k)*((1+(h : ℝ))/(k : ℝ)) :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg hkR.le (collisionWeight_nonneg k))
    _ = _ := by field_simp

theorem resetShiftTrace_summable (h N : ℕ) : Summable (fun k => resetShiftTrace k h N) :=
  Summable.of_nonneg_of_le (fun k => resetShiftTrace_nonneg k h N)
    (fun k => resetShiftTrace_bound k h N) (collisionWeight_summable.mul_left (1+(h : ℝ)))

theorem resetPartial_integer_error (M : ℕ) {n : ℕ} (hn : 0<n) :
    ‖resetFunction (integerPhase n)-resetPartial M (integerPhase n)‖ =
      ∑' k, resetTerm (k+(M+1)) (integerPhase n) := by
  have he := (resetTerm_trace_summable hn).sum_add_tsum_nat_add (M+1)
  change resetPartial M (integerPhase n)+(∑' k, resetTerm (k+(M+1)) (integerPhase n)) =
    resetFunction (integerPhase n) at he
  rw [← he, add_sub_cancel_left]
  exact Real.norm_of_nonneg (tsum_nonneg (fun k => resetTerm_nonneg _ _))

theorem resetPartial_integer_L1_error (M h N : ℕ) :
    orbitAverage N (fun n => ‖resetFunction (integerPhase (n+h : ℕ))-
      resetPartial M (integerPhase (n+h : ℕ))‖)≤(1+(h : ℝ))*tailMass M := by
  have he : orbitAverage N (fun n => ‖resetFunction (integerPhase (n+h : ℕ))-
      resetPartial M (integerPhase (n+h : ℕ))‖) =
      ∑' k, resetShiftTrace (k+(M+1)) h N := by
    unfold resetShiftTrace orbitAverage
    rw [tsum_div_const]
    congr 1
    have hs (n : ℕ) (_ : n ∈ Finset.range N) :
        Summable (fun k => resetTerm (k+(M+1)) (integerPhase (n+1+h : ℕ))) := by
      have hs := (resetTerm_trace_summable (by omega : 0<n+1+h)).comp_injective
        (fun _ _ he => Nat.add_right_cancel he : Function.Injective (fun k : ℕ => k+(M+1)))
      convert! hs using 1
    change (∑ n ∈ Finset.range N, ‖resetFunction (integerPhase (n+1+h : ℕ))-
      resetPartial M (integerPhase (n+1+h : ℕ))‖) =
        ∑' k, ∑ n ∈ Finset.range N, resetTerm (k+(M+1)) (integerPhase (n+1+h : ℕ))
    rw [Summable.tsum_finsetSum hs]
    exact Finset.sum_congr rfl (fun n _ => resetPartial_integer_error M (by omega))
  rw [he]
  have hs := (resetShiftTrace_summable h N).comp_injective
    (fun _ _ he => Nat.add_right_cancel he : Function.Injective (fun k : ℕ => k+(M+1)))
  have hw := collisionWeight_summable.comp_injective
    (fun _ _ he => Nat.add_right_cancel he : Function.Injective (fun k : ℕ => k+(M+1)))
  convert! hs.tsum_le_tsum (fun k => resetShiftTrace_bound (k+(M+1)) h N)
    (hw.mul_left (1+(h : ℝ))) using 1
  exact tsum_mul_left.symm

theorem locallyConstant_finite_pi {ι : Type*} [Finite ι] (f : ι → Phase → ℝ)
    (hf : ∀ i, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x i => f i x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have he := Filter.eventually_all.mpr (fun i => (hf i).eventually_eq x)
  filter_upwards [he] with y hy
  exact funext hy

theorem finite_pi_norm_le_sum {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖≤∑ i, ‖v i‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro i
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem orbitAverage_mono (N : ℕ) {f g : ℕ → ℝ} (hfg : ∀ n, f n≤g n) :
    orbitAverage N f≤orbitAverage N g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hfg (n+1))) (Nat.cast_nonneg N)

theorem orbitAverage_norm_bound (N : ℕ) (f : ℕ → ℝ) :
    ‖orbitAverage N f‖≤orbitAverage N (fun n => ‖f n‖) := by
  unfold orbitAverage
  rw [norm_div, Real.norm_of_nonneg (Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg N)

theorem orbitAverage_sub (N : ℕ) (f g : ℕ → ℝ) :
    orbitAverage N (fun n => f n-g n)=orbitAverage N f-orbitAverage N g := by
  unfold orbitAverage
  rw [Finset.sum_sub_distrib, sub_div]

theorem orbitAverage_const_mul (N : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    orbitAverage N (fun n => a*f n)=a*orbitAverage N f := by
  unfold orbitAverage
  rw [← Finset.mul_sum, mul_div_assoc]

theorem orbitAverage_finsetSum {ι : Type*} (N : ℕ) (S : Finset ι) (f : ι → ℕ → ℝ) :
    orbitAverage N (fun n => ∑ i ∈ S, f i n)=∑ i ∈ S, orbitAverage N (f i) := by
  unfold orbitAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem tendsto_of_uniform_approximations (F : ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (I : ℝ) (J B : ℕ → ℝ)
    (hB : Tendsto B atTop (nhds 0))
    (hA : ∀ M, Tendsto (A M) atTop (nhds (J M)))
    (hF : ∀ M N, ‖F N-A M N‖≤B M) (hI : ∀ M, ‖I-J M‖≤B M) :
    Tendsto F atTop (nhds I) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := ((tendsto_order.mp hB).2 (ε/4) (by linarith)).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hA M) (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have ha := hN n hn
  rw [dist_eq_norm] at ha ⊢
  have ht : ‖F n-I‖≤‖F n-A M n‖+‖A M n-J M‖+‖I-J M‖ := by
    calc
      _ ≤ ‖F n-A M n‖+‖A M n-I‖ := by
        simpa only [dist_eq_norm] using dist_triangle (F n) (A M n) I
      _ ≤ ‖F n-A M n‖+(‖A M n-J M‖+‖J M-I‖) := by
        have hb := dist_triangle (A M n) (J M) I
        simp only [dist_eq_norm] at hb
        linarith
      _ = _ := by rw [norm_sub_rev (J M) I]; ring
  linarith [hF M n, hI M]

end NField.Alignment.CollisionIntegerLawApproximation
