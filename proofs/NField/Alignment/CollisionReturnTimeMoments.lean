/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReturnPairCounting
import NField.Alignment.CollisionPotentialCoboundary

/-!
# Stationary return counts on the actual collision Haar space

The indicators can be dependent. Translation invariance identifies each
pair integral with a return probability; the coefficient N-h is an exact
finite count. Null measurable events are allowed because the potential
is represented by an L2 equivalence class.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionReturnTimeMoments

open scoped BigOperators Classical ENNReal
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialCoboundary
open CollisionReturnPairCounting

def visitIndicator (A : Set Phase) (j : ℕ) (x : Phase) : ℝ :=
  A.indicator (fun _ => 1) (CollisionPotentialCoboundary.translate (j : ℤ) x)

def visitCount (A : Set Phase) (N : ℕ) (x : Phase) : ℝ :=
  ∑ j∈Finset.range N, visitIndicator A j x

def returnProbability (A : Set Phase) (h : ℕ) : ℝ :=
  phaseHaar.real (A ∩ CollisionPotentialCoboundary.translate (h : ℤ) ⁻¹' A)

theorem visitIndicator_integrable {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (j : ℕ) : Integrable (visitIndicator A j) phaseHaar := by
  have he : visitIndicator A j=
      (CollisionPotentialCoboundary.translate (j : ℤ) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [visitIndicator,Set.indicator_apply,Set.mem_preimage]
  rw [he]
  exact (integrable_const (1 : ℝ)).indicator₀
    (hA.preimage (translate_measurePreserving (j : ℤ)).quasiMeasurePreserving)

theorem indicator_integral {A : Set Phase} (hA : NullMeasurableSet A phaseHaar) :
    (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂phaseHaar)=phaseHaar.real A := by
  rw [integral_indicator₀ hA,setIntegral_const]
  simp

theorem visitIndicator_mean {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (j : ℕ) : (∫ x, visitIndicator A j x ∂phaseHaar)=phaseHaar.real A := by
  exact ((translate_measurePreserving (j : ℤ)).integral_comp
    (MeasurableEquiv.mulLeft (integerPhase (j : ℤ))).measurableEmbedding
    (A.indicator (fun _ => (1 : ℝ)))).trans (indicator_integral hA)

theorem visitIndicator_sq (A : Set Phase) (j : ℕ) (x : Phase) :
    visitIndicator A j x^2=visitIndicator A j x := by
  simp only [visitIndicator,Set.indicator_apply]
  split_ifs <;> norm_num

theorem visitIndicator_norm_le_one (A : Set Phase) (j : ℕ) (x : Phase) :
    ‖visitIndicator A j x‖≤1 := by
  simp only [visitIndicator,Set.indicator_apply]
  split_ifs <;> norm_num

theorem visitIndicator_pair (A : Set Phase) (i j : ℕ) :
    (fun x => visitIndicator A i x*visitIndicator A j x)=
      ((CollisionPotentialCoboundary.translate (i : ℤ) ⁻¹' A) ∩
        (CollisionPotentialCoboundary.translate (j : ℤ) ⁻¹' A)).indicator (fun _ => 1) := by
  funext x
  simp only [visitIndicator,Set.indicator_apply,Set.mem_inter_iff,Set.mem_preimage]
  split_ifs <;> simp_all

theorem visitIndicator_pair_integrable {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (i j : ℕ) : Integrable (fun x => visitIndicator A i x*visitIndicator A j x) phaseHaar := by
  rw [visitIndicator_pair]
  exact (integrable_const (1 : ℝ)).indicator₀
    ((hA.preimage (translate_measurePreserving (i : ℤ)).quasiMeasurePreserving).inter
      (hA.preimage (translate_measurePreserving (j : ℤ)).quasiMeasurePreserving))

theorem visitIndicator_pair_mean {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    {i j : ℕ} (hij : i≤j) :
    (∫ x, visitIndicator A i x*visitIndicator A j x ∂phaseHaar)=returnProbability A (j-i) := by
  have he : (fun x => visitIndicator A i x*visitIndicator A j x)=
      (fun x => (A ∩ CollisionPotentialCoboundary.translate ((j-i : ℕ) : ℤ) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)) (CollisionPotentialCoboundary.translate (i : ℤ) x)) := by
    funext x
    have hs : CollisionPotentialCoboundary.translate ((j-i : ℕ) : ℤ)
        (CollisionPotentialCoboundary.translate (i : ℤ) x)=
        CollisionPotentialCoboundary.translate (j : ℤ) x := by
      rw [← translate_add]
      congr 1
      omega
    simp only [visitIndicator,Set.indicator_apply,Set.mem_inter_iff,Set.mem_preimage,hs]
    split_ifs <;> simp_all
  rw [he]
  exact ((translate_measurePreserving (i : ℤ)).integral_comp
    (MeasurableEquiv.mulLeft (integerPhase (i : ℤ))).measurableEmbedding _).trans
      (indicator_integral (hA.inter
        (hA.preimage (translate_measurePreserving ((j-i : ℕ) : ℤ)).quasiMeasurePreserving)))

theorem visitCount_integrable {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N : ℕ) : Integrable (visitCount A N) phaseHaar :=
  integrable_finsetSum _ (fun j _ => visitIndicator_integrable hA j)

theorem visitCount_norm_bound (A : Set Phase) (N : ℕ) (x : Phase) :
    ‖visitCount A N x‖≤(N : ℝ) := by
  calc
    _ ≤ ∑ j∈Finset.range N, ‖visitIndicator A j x‖ := norm_sum_le _ _
    _ ≤ ∑ _j∈Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => visitIndicator_norm_le_one A j x)
    _ = _ := by simp

theorem visitCount_sq_integrable {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N : ℕ) : Integrable (fun x => visitCount A N x^2) phaseHaar := by
  have hm : MemLp (visitCount A N) 2 phaseHaar := MemLp.of_bound
    (visitCount_integrable hA N).aestronglyMeasurable (N : ℝ)
      (Filter.Eventually.of_forall (visitCount_norm_bound A N))
  exact hm.integrable_sq

theorem visitCount_mean {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N : ℕ) : (∫ x, visitCount A N x ∂phaseHaar)=(N : ℝ)*phaseHaar.real A := by
  unfold visitCount
  rw [integral_finsetSum _ (fun j _ => visitIndicator_integrable hA j)]
  simp only [visitIndicator_mean hA,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem visitCount_cross_integrable {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N j : ℕ) : Integrable (fun x => visitCount A N x*visitIndicator A j x) phaseHaar := by
  simp only [visitCount,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => visitIndicator_pair_integrable hA i j)

theorem visitCount_cross_mean {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N : ℕ) : (∫ x, visitCount A N x*visitIndicator A N x ∂phaseHaar)=
      ∑ h∈Finset.range N, returnProbability A (h+1) := by
  simp only [visitCount,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => visitIndicator_pair_integrable hA i N)]
  rw [← reverse_gap_sum]
  exact Finset.sum_congr rfl (fun i hi => visitIndicator_pair_mean hA
    (Nat.le_of_lt (Finset.mem_range.mp hi)))

theorem visitCount_succ (A : Set Phase) (N : ℕ) (x : Phase) :
    visitCount A (N+1) x=visitCount A N x+visitIndicator A N x := by
  exact Finset.sum_range_succ _ _

theorem visitCount_second_moment {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    (N : ℕ) : (∫ x, visitCount A N x^2 ∂phaseHaar)=
      (N : ℝ)*phaseHaar.real A+2*weightedGapSum (returnProbability A) N := by
  induction N with
  | zero => simp [visitCount,weightedGapSum]
  | succ N ih =>
    have he : (fun x => visitCount A (N+1) x^2)=
        (fun x => visitCount A N x^2+2*(visitCount A N x*visitIndicator A N x)+
          visitIndicator A N x) := by
      funext x
      rw [visitCount_succ]
      nlinarith [visitIndicator_sq A N x]
    have hi : Integrable (fun x => visitCount A N x^2+
        2*(visitCount A N x*visitIndicator A N x)) phaseHaar :=
      (visitCount_sq_integrable hA N).add ((visitCount_cross_integrable hA N N).const_mul 2)
    rw [he,integral_add hi (visitIndicator_integrable hA N),
      integral_add (visitCount_sq_integrable hA N)
        ((visitCount_cross_integrable hA N N).const_mul 2),integral_const_mul,ih,
      visitCount_cross_mean hA,visitIndicator_mean hA,weightedGapSum_succ]
    push_cast
    ring

theorem square_mean_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ) :
    (∫ x, f x ∂μ)^2≤∫ x, f x^2 ∂μ := by
  let m : ℝ := ∫ x, f x ∂μ
  have hle := integral_mono ((hf.const_mul (2*m)).sub (integrable_const (m^2))) hf2
    (fun x => show 2*m*f x-m^2≤f x^2 by nlinarith [sq_nonneg (f x-m)])
  change (∫ x, 2*m*f x-m^2 ∂μ)≤_ at hle
  rw [integral_sub (hf.const_mul (2*m)) (integrable_const (m^2)),integral_const_mul,
    integral_const] at hle
  simp only [probReal_univ,smul_eq_mul,one_mul] at hle
  change (2*m)*m-m^2≤_ at hle
  change m^2≤_
  nlinarith

theorem stationary_recurrence {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    {N : ℕ} (hN : 0<N) : (phaseHaar.real A)^2≤phaseHaar.real A/(N : ℝ)+
      2/(N : ℝ)^2*weightedGapSum (returnProbability A) N := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have h := square_mean_le_second_moment (visitCount_integrable hA N)
    (visitCount_sq_integrable hA N)
  rw [visitCount_mean hA,visitCount_second_moment hA] at h
  have hd := div_le_div_of_nonneg_right h (sq_nonneg (N : ℝ))
  have hl : ((N : ℝ)*phaseHaar.real A)^2/(N : ℝ)^2=(phaseHaar.real A)^2 := by
    field_simp
  have hr : ((N : ℝ)*phaseHaar.real A+2*weightedGapSum (returnProbability A) N)/(N : ℝ)^2=
      phaseHaar.real A/(N : ℝ)+2/(N : ℝ)^2*weightedGapSum (returnProbability A) N := by
    field_simp
  rwa [hl,hr] at hd

theorem stationary_recurrence_Icc {A : Set Phase} (hA : NullMeasurableSet A phaseHaar)
    {N : ℕ} (hN : 0<N) : (phaseHaar.real A)^2≤phaseHaar.real A/(N : ℝ)+
      2/(N : ℝ)^2*(∑ h∈Finset.Icc 1 (N-1), ((N : ℝ)-(h : ℝ))*
        phaseHaar.real (A ∩ CollisionPotentialCoboundary.translate (h : ℤ) ⁻¹' A)) := by
  simpa only [weightedGapSum_Icc,returnProbability] using stationary_recurrence hA hN

end NField.Alignment.CollisionReturnTimeMoments
