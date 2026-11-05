/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProfiniteOdometerErgodic
import NField.Alignment.CollisionCycleStationarity
import NField.Alignment.CollisionL1Testing
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Measure.OpenPos

/-!+# Periodic tests on the profinite integer orbit

Every locally constant test has an actual positive integer period. Compactness
makes its translation stabilizer open; the finite quotient supplies the period.
The orbit averages below begin at the positive integer one.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ProfinitePeriodicTesting

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialCoboundary ProfiniteOdometerErgodic CollisionCycleStationarity

local notation "phaseTranslate" => CollisionPotentialCoboundary.translate

def translationStabilizer (f : Phase → ℝ) : Subgroup Phase where
  carrier := {y | ∀ x, f (y*x)=f x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [mul_assoc, ha, hb]
  inv_mem' := by
    intro a ha x
    simpa using (ha (a⁻¹*x)).symm

theorem translationStabilizer_open (f : LocallyConstant Phase ℝ) :
    IsOpen (translationStabilizer f : Set Phase) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  change {y : Phase | ∀ x, f (y*x)=f x} ∈ nhds 1
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun y x : Phase => f (y*x)=f x) (x₀ := (1 : Phase)) (fun x _ => ?_)
  · convert! h using 1
    simp only [Set.mem_univ, forall_true_left]
    rfl
  · have ht : Tendsto (fun z : Phase × Phase => z.1*z.2) (nhds (1,x)) (nhds x) := by
      simpa only [one_mul] using
        (show Continuous (fun z : Phase × Phase => z.1*z.2) from
          continuous_fst.mul continuous_snd).tendsto (1,x)
    have hmul : ∀ᶠ z : Phase × Phase in nhds (1,x), f (z.1*z.2)=f x :=
      ht.eventually (f.isLocallyConstant.eventually_eq x)
    have hsnd : ∀ᶠ z : Phase × Phase in nhds (1,x), f z.2=f x :=
      (show Tendsto (fun z : Phase × Phase => z.2) (nhds (1,x)) (nhds x) from
        continuous_snd.continuousAt).eventually (f.isLocallyConstant.eventually_eq x)
    filter_upwards [hmul, hsnd] with z hz hz'
    exact hz.trans hz'.symm

theorem locallyConstant_integer_period (f : LocallyConstant Phase ℝ) :
    ∃ L : ℕ, 0<L ∧ ∀ x, f (phaseTranslate L x)=f x := by
  let H := translationStabilizer f
  letI : Finite (Phase ⧸ H) := H.quotient_finite_of_isOpen (translationStabilizer_open f)
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨H.index, Nat.pos_of_ne_zero H.index_ne_zero_of_finite, ?_⟩
  intro x
  have h := H.pow_index_mem (integerPhase 1)
  change ∀ x, f (integerPhase 1 ^ H.index*x)=f x at h
  change f (integerPhase (H.index : ℤ)*x)=f x
  rw [integerPhase_zpow (H.index : ℤ), zpow_natCast]
  exact h x

def orbitAverage (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, f (n+1))/(N : ℝ)

def phaseCycleMean (f : C(Phase, ℝ)) (L : ℕ) (x : Phase) : ℝ :=
  (∑ n ∈ Finset.range L, f (phaseTranslate n x))/(L : ℝ)

theorem phaseCycleMean_continuous (f : C(Phase, ℝ)) (L : ℕ) :
    Continuous (phaseCycleMean f L) := by
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun n _ => f.continuous.comp (continuous_const.mul continuous_id))

theorem phaseCycleMean_invariant (f : C(Phase, ℝ)) (L : ℕ)
    (hL : ∀ x, f (phaseTranslate L x)=f x) (x : Phase) :
    phaseCycleMean f L (phaseTranslate 1 x)=phaseCycleMean f L x := by
  unfold phaseCycleMean
  congr 1
  have hs := Finset.sum_range_succ' (fun n : ℕ => f (phaseTranslate n x)) L
  rw [Finset.sum_range_succ, hL, Nat.cast_zero, translate_zero] at hs
  have he : (∑ n ∈ Finset.range L, f (phaseTranslate n (phaseTranslate 1 x))) =
      ∑ n ∈ Finset.range L, f (phaseTranslate (n+1 : ℕ) x) := by
    apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg f (translate_add (n : ℤ) 1 x).symm
  rw [he]
  exact (add_right_cancel hs).symm

theorem continuous_phase_integrable (f : C(Phase, ℝ)) : Integrable f phaseHaar := by
  exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem phaseCycleMean_integral (f : C(Phase, ℝ)) {L : ℕ} (hL : 0<L) :
    (∫ x, phaseCycleMean f L x ∂phaseHaar) = ∫ x, f x ∂phaseHaar := by
  have hi (n : ℕ) : Integrable (fun x => f (phaseTranslate n x)) phaseHaar :=
    continuous_phase_integrable
      ⟨_, f.continuous.comp (continuous_const.mul continuous_id)⟩
  unfold phaseCycleMean
  rw [integral_div, integral_finsetSum _ (fun n _ => hi n)]
  simp only [CollisionPotentialCoboundary.translate, integral_mul_left_eq_self,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

theorem phaseCycleMean_eq_integral (f : C(Phase, ℝ)) {L : ℕ} (hL : 0<L)
    (hp : ∀ x, f (phaseTranslate L x)=f x) (x : Phase) :
    phaseCycleMean f L x = ∫ y, f y ∂phaseHaar := by
  let F : C(Phase, ℝ) := ⟨phaseCycleMean f L, phaseCycleMean_continuous f L⟩
  let V : HaarL2 := ContinuousMap.toLp 2 phaseHaar ℝ F
  have hV : (fun x => V x) =ᵐ[phaseHaar] F :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar F
  have hinv : shift 1 V=V := by
    apply Lp.ext
    have htrans := (translate_measurePreserving 1).quasiMeasurePreserving.ae hV
    filter_upwards [shift_coe 1 V, hV, htrans] with y hy hy' hty
    rw [hy, hty, hy']
    exact phaseCycleMean_invariant f L hp y
  obtain ⟨c,hc⟩ := translation_invariant_constant V hinv
  have hF : (F : Phase → ℝ) = fun _ => c :=
    Measure.eq_of_ae_eq (hV.symm.trans hc) F.continuous continuous_const
  have hmean := phaseCycleMean_integral f hL
  change (∫ y, F y ∂phaseHaar) = ∫ y, f y ∂phaseHaar at hmean
  rw [hF, integral_const, probReal_univ, one_smul] at hmean
  exact (congrFun hF x).trans hmean

theorem periodic_sum_error (f : ℕ → ℝ) {L : ℕ} (hL : 0<L)
    (hp : Function.Periodic f L) (N : ℕ) :
    |(∑ n ∈ Finset.range N, f n)-(N : ℝ)*
      ((∑ n ∈ Finset.range L, f n)/(L : ℝ))| ≤
        2*∑ n ∈ Finset.range L, |f n| := by
  let S := ∑ n ∈ Finset.range L, f n
  let K := ∑ n ∈ Finset.range L, |f n|
  have hLR : (0 : ℝ)<L := by exact_mod_cast hL
  have hrem : (N%L : ℕ) < L := Nat.mod_lt N hL
  have hN : (N : ℝ) = (N/L : ℕ)*(L : ℝ)+(N%L : ℕ) := by
    exact_mod_cast (show N=(N/L)*L+N%L by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N L).symm)
  have hpart : |∑ n ∈ Finset.range (N%L), f n| ≤ K := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrem.le)
      (fun n _ _ => abs_nonneg (f n))
  have hS : |S| ≤ K := Finset.abs_sum_le_sum_abs _ _
  rw [periodic_sum_decomposition f L N hp]
  change |(N/L : ℕ)*S+(∑ n ∈ Finset.range (N%L), f n)-(N : ℝ)*(S/L)| ≤ 2*K
  have he : (N/L : ℕ)*S+(∑ n ∈ Finset.range (N%L), f n)-(N : ℝ)*(S/L) =
      (∑ n ∈ Finset.range (N%L), f n)-((N%L : ℕ) : ℝ)/L*S := by
    rw [hN]
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  have hratio : 0 ≤ ((N%L : ℕ) : ℝ)/L ∧ ((N%L : ℕ) : ℝ)/L ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hLR).mpr (by exact_mod_cast hrem.le)
  rw [abs_mul, abs_of_nonneg hratio.1]
  have hprod := mul_le_mul_of_nonneg_right hratio.2 (abs_nonneg S)
  linarith

theorem periodic_average_tendsto (f : ℕ → ℝ) {L : ℕ} (hL : 0<L)
    (hp : Function.Periodic f L) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n)/(N : ℝ)) atTop
      (nhds ((∑ n ∈ Finset.range L, f n)/(L : ℝ))) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  refine squeeze_zero (fun N => abs_nonneg _) (fun N => show _ ≤
    (2*∑ n ∈ Finset.range L, |f n|)/((N+1 : ℕ) : ℝ) from ?_) ?_
  · have hNR : (0 : ℝ)<(N+1 : ℕ) := by positivity
    have he : (∑ n ∈ Finset.range (N+1), f n)/((N+1 : ℕ) : ℝ)-
        (∑ n ∈ Finset.range L, f n)/(L : ℝ) =
        ((∑ n ∈ Finset.range (N+1), f n)-((N+1 : ℕ) : ℝ)*
          ((∑ n ∈ Finset.range L, f n)/(L : ℝ)))/((N+1 : ℕ) : ℝ) := by
      field_simp
    rw [he, abs_div, abs_of_pos hNR]
    exact div_le_div_of_nonneg_right (periodic_sum_error f hL hp (N+1)) hNR.le
  · have hi : Tendsto (fun N : ℕ => (((N+1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [div_eq_mul_inv, mul_zero] using
      hi.const_mul (2*∑ n ∈ Finset.range L, |f n|)

theorem locallyConstant_orbit_tendsto (f : LocallyConstant Phase ℝ) :
    Tendsto (fun N => orbitAverage N (fun n => f (integerPhase n))) atTop
      (nhds (∫ x, f x ∂phaseHaar)) := by
  obtain ⟨L,hL,hperiod⟩ := locallyConstant_integer_period f
  have hp : Function.Periodic (fun n : ℕ => f (integerPhase (n+1 : ℕ))) L := by
    intro n
    have hi : ((n+L+1 : ℕ) : ℤ)=(L : ℤ)+((n+1 : ℕ) : ℤ) := by omega
    change f (integerPhase (n+L+1 : ℕ))=f (integerPhase (n+1 : ℕ))
    rw [hi, integerPhase_add]
    exact hperiod (integerPhase (n+1 : ℕ))
  have hm := phaseCycleMean_eq_integral (f : C(Phase, ℝ)) hL hperiod (integerPhase 1)
  have hs : (∑ n ∈ Finset.range L, f (integerPhase (n+1 : ℕ)))/(L : ℝ) =
      ∫ x, f x ∂phaseHaar := by
    convert! hm using 1
  have h := periodic_average_tendsto _ hL hp
  rw [hs] at h
  exact h

theorem locallyConstant_continuous_dense :
    DenseRange (fun f : LocallyConstant Phase ℝ => (f : C(Phase, ℝ))) := by
  rw [DenseRange, dense_iff_closure_eq]
  let A : Subalgebra ℝ C(Phase, ℝ) := (LocallyConstant.toContinuousMapAlgHom ℝ).range
  change closure (A : Set C(Phase, ℝ)) = Set.univ
  rw [← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (LocallyConstant.separatesPoints_range_toContinuousMapAlgHom ℝ)]
  rfl

theorem locallyConstant_L2_dense :
    DenseRange (fun f : LocallyConstant Phase ℝ =>
      ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase, ℝ))) := by
  exact (ContinuousMap.toLp_denseRange (p := 2) ℝ phaseHaar ℝ (by norm_num)).comp
    locallyConstant_continuous_dense (ContinuousMap.toLp 2 phaseHaar ℝ).continuous

theorem locallyConstant_L2_separates (F G : HaarL2)
    (h : ∀ f : LocallyConstant Phase ℝ,
      (∫ x, F x*f x ∂phaseHaar) = ∫ x, G x*f x ∂phaseHaar) : F=G := by
  apply ext_inner_right ℝ
  have he := locallyConstant_L2_dense.equalizer
    (show Continuous (fun V : HaarL2 => inner ℝ F V) from continuous_const.inner continuous_id)
    (show Continuous (fun V : HaarL2 => inner ℝ G V) from continuous_const.inner continuous_id)
  have htest : (fun f : LocallyConstant Phase ℝ =>
      inner ℝ F (ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase, ℝ)))) =
      (fun f : LocallyConstant Phase ℝ =>
      inner ℝ G (ContinuousMap.toLp 2 phaseHaar ℝ (f : C(Phase, ℝ)))) := by
    funext f
    rw [← CollisionL1Testing.continuousTest_lowerL2,
      ← CollisionL1Testing.continuousTest_lowerL2]
    exact h f
  exact fun V => congrFun (he htest) V

end NField.Alignment.ProfinitePeriodicTesting
