/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerDiscretization

/-!
# The unit integral compared with the actual discrete Euler-product samples

Disjoint half-open grid cells cover the whole unit interval when the grid
scale is a positive integer, including both parity cases at the boundary.
Translation and a squared triangle inequality bound the integral by twice
the discrete sample energy plus twice the literal grid error. Integrability
and the fractional comparison through the actual box functional are proved.
At the manuscript's rounded cutoff all integer-grid hypotheses are proved.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperEulerGridComparison
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSmoothCount
  HarperRandomEulerProduct HarperEulerIntegral HarperEulerSecondMoment HarperEulerIncrement
  HarperEulerDiscretization HarperFrequencyIntervals HarperRoundedCutoff

def gridCell (D v : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ioc (v+((k : ℝ)-1/2)/D) (v+((k : ℝ)+1/2)/D)
def discreteEnergy (P v : ℝ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale P),
    ‖eulerProduct P (linePoint (1/2) (v+(k : ℝ)/gridScale P)) ω‖^2)/gridScale P

theorem gridCell_disjoint {D : ℝ} (hD : 0 < D) (v : ℝ) {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (gridCell D v k) (gridCell D v l) := by
  suffices h : ∀ k l : ℤ, k < l → Disjoint (gridCell D v k) (gridCell D v l) from
    (lt_or_gt_of_ne hkl).elim (h k l) (fun hh => (h l k hh).symm)
  intro k l hlt
  apply Set.disjoint_left.mpr
  intro t ht hu
  have hstep : (k : ℝ)+1 ≤ (l : ℝ) := by exact_mod_cast (show k+1 ≤ l by omega)
  have hed : ((k : ℝ)+1/2)/D ≤ ((l : ℝ)-1/2)/D :=
    div_le_div_of_nonneg_right (by linarith) hD.le
  exact (not_lt_of_ge (ht.2.trans (by linarith))) hu.1

theorem gridCells_cover {d : ℕ} (hd : 0 < d) (v : ℝ) :
    Set.Ioc (v-1/2) (v+1/2) ⊆ ⋃ k ∈ gridCenters (d : ℝ), gridCell (d : ℝ) v k := by
  intro t ht
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  let m : ℤ := ⌊(d : ℝ)/2⌋
  let k : ℤ := ⌈(d : ℝ)*(t-v)-1/2⌉
  have hm : (d : ℝ)-1 ≤ 2*(m : ℝ) := by
    have hh : (d : ℝ)-2 < 2*(m : ℝ) := by
      have := Int.lt_floor_add_one ((d : ℝ)/2)
      dsimp only [m]
      linarith
    have hh' : (d : ℤ)-2 < 2*m := by exact_mod_cast hh
    exact_mod_cast (show (d : ℤ)-1 ≤ 2*m by omega)
  have htlo : -(d : ℝ)/2 < (d : ℝ)*(t-v) := by nlinarith [ht.1]
  have hthi : (d : ℝ)*(t-v) ≤ (d : ℝ)/2 := by nlinarith [ht.2]
  have hklo : -m ≤ k := by
    have hh : (-m-1 : ℤ) < k := Int.lt_ceil.mpr (by push_cast; linarith)
    omega
  have hkhi : k ≤ m := Int.ceil_le.mpr (by linarith)
  have hkg : k ∈ gridCenters (d : ℝ) := by
    simp only [gridCenters, Finset.mem_Icc, Int.ceil_neg]
    exact ⟨hklo,hkhi⟩
  refine Set.mem_iUnion.mpr ⟨k,?_⟩
  refine Set.mem_iUnion.mpr ⟨hkg,?_⟩
  have hkle := Int.le_ceil ((d : ℝ)*(t-v)-1/2)
  have hklt := Int.ceil_lt_add_one ((d : ℝ)*(t-v)-1/2)
  constructor
  · change v+((k : ℝ)-1/2)/(d : ℝ) < t
    have hh : ((k : ℝ)-1/2)/(d : ℝ) < t-v := by
      apply (div_lt_iff₀ hD).mpr
      dsimp only [k]
      nlinarith
    linarith
  · change t ≤ v+((k : ℝ)+1/2)/(d : ℝ)
    apply (sub_le_iff_le_add').mp
    apply (le_div_iff₀ hD).mpr
    dsimp only [k]
    nlinarith


theorem verticalEnergy_integrable_line (P a b : ℝ) (ω : PhaseSpace) :
    Integrable (fun t => verticalEnergy P (1/2) (t,ω)) (volume.restrict (Set.Ioc a b)) := by
  apply Integrable.of_bound (((verticalProduct_measurable P (1/2)).comp
    (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable
    ((shiftedProduct P (1/2))^2)
  apply Filter.Eventually.of_forall
  intro t
  change ‖verticalEnergy P (1/2) (t,ω)‖ ≤ _
  rw [Real.norm_of_nonneg (show 0 ≤ verticalEnergy P (1/2) (t,ω) from sq_nonneg _)]
  have h := eulerProduct_norm_le P (s := linePoint (1/2) t) (by norm_num [linePoint_re]) ω
  rw [linePoint_re] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem shiftedEnergy_integrable (P u h : ℝ) (ω : PhaseSpace) :
    Integrable (fun t => verticalEnergy P (1/2) (u+t,ω)) (volume.restrict (Set.Ioc (-h) h)) := by
  apply Integrable.of_bound (((verticalProduct_measurable P (1/2)).comp
    ((measurable_const.add measurable_id).prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable
    ((shiftedProduct P (1/2))^2)
  apply Filter.Eventually.of_forall
  intro t
  change ‖verticalEnergy P (1/2) (u+t,ω)‖ ≤ _
  rw [Real.norm_of_nonneg (show 0 ≤ verticalEnergy P (1/2) (u+t,ω) from sq_nonneg _)]
  have hb := eulerProduct_norm_le P (s := linePoint (1/2) (u+t)) (by norm_num [linePoint_re]) ω
  rw [linePoint_re] at hb
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem verticalEnergy_le_sample_and_increment (P u t : ℝ) (ω : PhaseSpace) :
    verticalEnergy P (1/2) (u+t,ω) ≤
      2*verticalEnergy P (1/2) (u,ω)+2*incrementEnergy P u t ω := by
  let a := eulerProduct P (linePoint (1/2) (u+t)) ω
  let b := eulerProduct P (linePoint (1/2) u) ω
  change ‖a‖^2 ≤ 2*‖b‖^2+2*‖a-b‖^2
  have hn : ‖a‖ ≤ ‖b‖+‖a-b‖ := by simpa only [add_sub_cancel] using norm_add_le b (a-b)
  have hs := pow_le_pow_left₀ (norm_nonneg a) hn 2
  nlinarith [sq_nonneg (‖b‖-‖a-b‖)]

theorem gridCell_integral_eq (P v : ℝ) {D : ℝ} (hD : 0 < D) (k : ℤ) (ω : PhaseSpace) :
    (∫ s in gridCell D v k, verticalEnergy P (1/2) (s,ω)) =
      ∫ t in Set.Ioc (-(1/(2*D))) (1/(2*D)),
        verticalEnergy P (1/2) (v+(k : ℝ)/D+t,ω) := by
  have hh : -(1/(2*D)) ≤ 1/(2*D) := by
    have : 0 ≤ 1/(2*D) := by positivity
    linarith
  have he := intervalIntegral.integral_comp_add_left
    (fun s => verticalEnergy P (1/2) (s,ω)) (v+(k : ℝ)/D)
    (a := -(1/(2*D))) (b := 1/(2*D))
  rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le (by linarith)] at he
  have ha : v+(k : ℝ)/D+ -(1/(2*D)) = v+((k : ℝ)-1/2)/D := by ring
  have hb : v+(k : ℝ)/D+1/(2*D) = v+((k : ℝ)+1/2)/D := by ring
  rw [ha,hb] at he
  exact he.symm

theorem gridCell_integral_bound (P v : ℝ) {D : ℝ} (hD : 0 < D) (k : ℤ) (ω : PhaseSpace) :
    (∫ s in gridCell D v k, verticalEnergy P (1/2) (s,ω)) ≤
      2*verticalEnergy P (1/2) (v+(k : ℝ)/D,ω)/D+
        2*cellError P (v+(k : ℝ)/D) (1/(2*D)) ω := by
  rw [gridCell_integral_eq P v hD]
  have hi := incrementEnergy_integrable_line P (v+(k : ℝ)/D) (1/(2*D)) ω
  calc
    _ ≤ ∫ t in Set.Ioc (-(1/(2*D))) (1/(2*D)),
        2*verticalEnergy P (1/2) (v+(k : ℝ)/D,ω)+
          2*incrementEnergy P (v+(k : ℝ)/D) t ω :=
      integral_mono (shiftedEnergy_integrable P _ _ ω)
        ((integrable_const _).add (hi.const_mul _))
        (fun t => verticalEnergy_le_sample_and_increment P _ t ω)
    _ = _ := by
      have hh : -(1/(2*D)) ≤ 1/(2*D) := by
        have : 0 ≤ 1/(2*D) := by positivity
        linarith
      rw [integral_add (integrable_const _) (hi.const_mul _)]
      simp only [integral_const_mul, integral_const, measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hh, smul_eq_mul, cellError]
      ring

theorem unitEnergy_le_discrete (P : ℝ) (v : ℤ) {d : ℕ} (hd : 0 < d)
    (hD : gridScale P = (d : ℝ)) (ω : PhaseSpace) :
    unitEnergy P v ω ≤ 2*discreteEnergy P v ω+2*gridError P v ω := by
  have hD0 : 0 < gridScale P := by rw [hD]; exact_mod_cast hd
  have hi : ∀ k ∈ gridCenters (gridScale P),
      IntegrableOn (fun t => verticalEnergy P (1/2) (t,ω)) (gridCell (gridScale P) v k) :=
    fun k _ => verticalEnergy_integrable_line P _ _ ω
  have hu := integrableOn_finset_iUnion.mpr hi
  have hsub : Set.Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2) ⊆
      ⋃ k ∈ gridCenters (gridScale P), gridCell (gridScale P) v k := by
    rw [hD]
    exact gridCells_cover hd v
  calc
    _ ≤ ∫ t in ⋃ k ∈ gridCenters (gridScale P), gridCell (gridScale P) v k,
        verticalEnergy P (1/2) (t,ω) :=
      setIntegral_mono_set hu (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall hsub)
    _ = ∑ k ∈ gridCenters (gridScale P),
        ∫ t in gridCell (gridScale P) v k, verticalEnergy P (1/2) (t,ω) :=
      integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc)
        (fun _ _ _ _ hkl => gridCell_disjoint hD0 _ hkl) hi
    _ ≤ ∑ k ∈ gridCenters (gridScale P),
        (2*verticalEnergy P (1/2) (v+(k : ℝ)/gridScale P,ω)/gridScale P+
          2*cellError P (v+(k : ℝ)/gridScale P) (1/(2*gridScale P)) ω) :=
      Finset.sum_le_sum (fun k _ => gridCell_integral_bound P v hD0 k ω)
    _ = _ := by
      unfold discreteEnergy gridError
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, verticalEnergy]
      ring

theorem actual_unitEnergy_le_discrete {x : ℝ} (hx : 0 < cutoffRoot x) (v : ℤ) (ω : PhaseSpace) :
    unitEnergy (primeCutoff x) v ω ≤
      2*discreteEnergy (primeCutoff x) v ω+2*gridError (primeCutoff x) v ω :=
  unitEnergy_le_discrete _ v (pow_pos hx 101) (gridScale_primeCutoff x) ω


theorem discreteEnergy_integrable (P v : ℝ) : Integrable (discreteEnergy P v) phaseMeasure := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro k _
  exact eulerProduct_norm_sq_integrable P (by norm_num [linePoint_re])

theorem discreteEnergy_nonneg {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) (ω : PhaseSpace) :
    0 ≤ discreteEnergy P v ω :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hD

theorem unitEnergy_conditioning_le_discrete {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : HarperActualConditioning.Coefficients p) (P : ℝ) (v : ℤ) {d : ℕ}
    (hd : 0 < d) (hD : gridScale P = (d : ℝ)) :
    HarperSmoothingConditioning.boxConditioning p c1 c2 (unitEnergy P v) ≤
      (2 : ℝ)^(3/4 : ℝ)*(HarperSmoothingConditioning.boxConditioning p c1 c2 (discreteEnergy P v)+
        (∫ ω, gridError P v ω ∂phaseMeasure)^(3/4 : ℝ)) := by
  have hD0 : 0 ≤ gridScale P := by rw [hD]; positivity
  have hdi := discreteEnergy_integrable P v
  have hgi := gridError_integrable P v
  have hbound (i : HarperActualConditioning.Boxes p) :
      HarperRoughSmoothing.boxMoment p c1 c2 i (unitEnergy P v) ≤
        2*HarperRoughSmoothing.boxMoment p c1 c2 i (discreteEnergy P v)+
          2*HarperRoughSmoothing.boxMoment p c1 c2 i (gridError P v) := by
    have h := HarperMainConditioning.boxMoment_mono hell c1 c2 i (unitEnergy_integrable P v)
      ((hdi.const_mul 2).add (hgi.const_mul 2)) (unitEnergy_le_discrete P v hd hD)
    have hiD := HarperRoughSmoothing.boxMoment_integrable hell c1 c2 i hdi
    have hiG := HarperRoughSmoothing.boxMoment_integrable hell c1 c2 i hgi
    have he : HarperRoughSmoothing.boxMoment p c1 c2 i
        (fun ω => 2*discreteEnergy P v ω+2*gridError P v ω) =
        2*HarperRoughSmoothing.boxMoment p c1 c2 i (discreteEnergy P v)+
          2*HarperRoughSmoothing.boxMoment p c1 c2 i (gridError P v) := by
      unfold HarperRoughSmoothing.boxMoment
      simp only [add_mul, mul_assoc]
      rw [integral_add (hiD.const_mul 2) (hiG.const_mul 2)]
      simp only [integral_const_mul]
    exact h.trans_eq he
  have h := HarperSmoothingConditioning.conditioning_split_bound
    (HarperActualConditioning.randomWeight p c1 c2)
    (fun i => HarperRoughSmoothing.boxMoment p c1 c2 i (unitEnergy P v))
    (fun i => HarperRoughSmoothing.boxMoment p c1 c2 i (discreteEnergy P v))
    (fun i => HarperRoughSmoothing.boxMoment p c1 c2 i (gridError P v))
    (HarperActualConditioning.randomWeight_nonneg hell c1 c2)
    (fun i => HarperRoughSmoothing.boxMoment_nonneg hell c1 c2 i (unitEnergy_nonneg P v))
    (fun i => HarperRoughSmoothing.boxMoment_nonneg hell c1 c2 i (discreteEnergy_nonneg hD0 v))
    (fun i => HarperRoughSmoothing.boxMoment_nonneg hell c1 c2 i (gridError_nonneg P v))
    (HarperRoughSmoothing.randomWeight_sum hell c1 c2) hbound
  rwa [HarperRoughSmoothing.boxMoment_sum hell c1 c2 hgi] at h

theorem actual_unitEnergy_conditioning_le_discrete {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : HarperActualConditioning.Coefficients p) (v : ℤ) :
    HarperSmoothingConditioning.boxConditioning p c1 c2
      (unitEnergy (primeCutoff ((p : ℝ)-1)) v) ≤
      (2 : ℝ)^(3/4 : ℝ)*(HarperSmoothingConditioning.boxConditioning p c1 c2
        (discreteEnergy (primeCutoff ((p : ℝ)-1)) v)+
        (∫ ω, gridError (primeCutoff ((p : ℝ)-1)) v ω ∂phaseMeasure)^(3/4 : ℝ)) := by
  have hr : 0 < cutoffRoot ((p : ℝ)-1) := by
    by_contra hn
    have he : cutoffRoot ((p : ℝ)-1) = 0 := Nat.eq_zero_of_not_pos hn
    simp [cutoffLog, he] at hell
  exact unitEnergy_conditioning_le_discrete hell c1 c2 _ v (pow_pos hr 101) (gridScale_primeCutoff _)

end NField.Alignment.HarperEulerGridComparison
