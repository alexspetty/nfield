/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianFirstCrossing

/-!
# First crossings and the Gaussian endpoint

At a first crossing, a nonnegative independent suffix endpoint keeps the
full endpoint above the crossed level. Summing disjoint first crossings
gives the discrete maximal inequality, including an empty final suffix.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianCrossingEndpoint
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperKilledPath HarperFirstCrossing
  HarperGaussianPathSplit HarperGaussianFirstCrossing HarperGaussianEndpoint HarperGaussianEndpointLaw

theorem gaussian_nonnegative_mass (v : NNReal) :
    (1/2 : ℝ) ≤ (gaussianReal 0 v).real (Ici (0 : ℝ)) := by
  by_cases hv : v = 0
  · subst v
    norm_num [measureReal_def]
  · have hp := gaussian_positive_half (pos_iff_ne_zero.mpr hv)
    have hm := measureReal_mono (μ := gaussianReal 0 v)
      (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self) (by finiteness)
    linarith

theorem gaussian_sum_upper_mass {n : ℕ} (v : Fin n → NNReal) (b : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real {z | b ≤ ∑ i, z i} =
      (gaussianReal 0 (∑ i, v i)).real (Ici b) := by
  have hm : Measurable (fun z : Fin n → ℝ => ∑ i, z i) := by fun_prop
  simp only [measureReal_def]
  rw [← gaussian_sum_law v,Measure.map_apply hm measurableSet_Ici]
  rfl

theorem gaussian_sum_nonnegative_mass {n : ℕ} (v : Fin n → NNReal) :
    (1/2 : ℝ) ≤ (Measure.pi (fun i => gaussianReal 0 (v i))).real {z | 0 ≤ ∑ i, z i} := by
  rw [gaussian_sum_upper_mass]
  exact gaussian_nonnegative_mass _

theorem crossing_nonnegative_suffix_cover {k n : ℕ} (b : ℝ) :
    firstCrossing b (Fin.last k) ×ˢ {z : Fin n → ℝ | 0 ≤ ∑ i, z i} ⊆
      (appendEquiv (k+1) n) ⁻¹'
        (firstCrossing b (Fin.castAdd n (Fin.last k)) ∩ {z | b ≤ ∑ i, z i}) := by
  intro p hp
  refine ⟨(firstCrossing_append_iff b (Fin.last k) p.1 p.2).mpr hp.1,?_⟩
  have hpre : b ≤ ∑ i, p.1 i := by simpa only [partialSum_last] using hp.1.1
  change b ≤ ∑ i, Fin.append p.1 p.2 i
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  have hsuf : (0 : ℝ) ≤ ∑ i, p.2 i := hp.2
  linarith

theorem gaussian_crossing_endpoint_half {k n : ℕ} (v : Fin ((k+1)+n) → NNReal) (b : ℝ) :
    (1/2 : ℝ)*(Measure.pi (fun i => gaussianReal 0 (v i))).real
      (firstCrossing b (Fin.castAdd n (Fin.last k))) ≤
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (firstCrossing b (Fin.castAdd n (Fin.last k)) ∩ {z | b ≤ ∑ i, z i}) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))
  let ν := Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd (k+1) i)))
  have hm : MeasurableSet {z : Fin ((k+1)+n) → ℝ | b ≤ ∑ i, z i} := by
    exact measurableSet_le measurable_const (by fun_prop)
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (firstCrossing b (Fin.castAdd n (Fin.last k)) ∩ {z | b ≤ ∑ i, z i}) =
      (μ.prod ν).real ((appendEquiv (k+1) n) ⁻¹'
        (firstCrossing b (Fin.castAdd n (Fin.last k)) ∩ {z | b ≤ ∑ i, z i})) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv (k+1) n).measurable
        ((measurableSet_firstCrossing b _).inter hm)]
  rw [he,gaussian_firstCrossing_prefix_mass]
  have hcover := measureReal_mono (μ := μ.prod ν)
    (crossing_nonnegative_suffix_cover (k := k) (n := n) b) (by finiteness)
  rw [measureReal_prod_prod] at hcover
  have hn := gaussian_sum_nonnegative_mass (fun i => v (Fin.natAdd (k+1) i))
  change (1/2 : ℝ) ≤ ν.real {z | 0 ≤ ∑ i, z i} at hn
  change (1/2 : ℝ)*μ.real (firstCrossing b (Fin.last k)) ≤ _
  calc
    _ ≤ μ.real (firstCrossing b (Fin.last k))*ν.real {z | 0 ≤ ∑ i, z i} := by
      nlinarith [mul_le_mul_of_nonneg_left hn
        (show 0 ≤ μ.real (firstCrossing b (Fin.last k)) from measureReal_nonneg)]
    _ ≤ _ := hcover

theorem gaussian_crossing_endpoint_half_index {N : ℕ} (v : Fin N → NNReal)
    (b : ℝ) (j : Fin N) :
    (1/2 : ℝ)*(Measure.pi (fun i => gaussianReal 0 (v i))).real (firstCrossing b j) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real
        (firstCrossing b j ∩ {z | b ≤ ∑ i, z i}) := by
  have hsplit : ∃ k n : ℕ, N = (k+1)+n ∧ j.val = k :=
    ⟨j.val,N-(j.val+1),by omega,rfl⟩
  obtain ⟨k,n,hN,hj⟩ := hsplit
  subst N
  have hj' : j = Fin.castAdd n (Fin.last k) := Fin.ext hj
  subst j
  exact gaussian_crossing_endpoint_half v b

theorem gaussian_maximal_endpoint_bound {n : ℕ} (v : Fin n → NNReal) (b : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real {z | ∃ j, b ≤ partialSum z j} ≤
      2*(gaussianReal 0 (∑ i, v i)).real (Ici b) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  let E : Set (Fin n → ℝ) := {z | b ≤ ∑ i, z i}
  have hE : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  have he : {z : Fin n → ℝ | ∃ j, b ≤ partialSum z j} = ⋃ j, firstCrossing b j := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    exact ⟨exists_firstCrossing b z,fun ⟨j,hj⟩ => ⟨j,hj.1⟩⟩
  have hd : Pairwise (fun i j : Fin n => Disjoint (firstCrossing b i ∩ E) (firstCrossing b j ∩ E)) :=
    fun i j hij => (firstCrossing_disjoint b hij).mono inter_subset_left inter_subset_left
  have hsub : (⋃ j : Fin n, firstCrossing b j ∩ E) ⊆ E := by
    intro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    exact hj.2
  have hsum := measureReal_mono (μ := μ) hsub (by finiteness)
  rw [measureReal_iUnion_fintype hd (fun j => (measurableSet_firstCrossing b j).inter hE)] at hsum
  have hhalf : (1/2 : ℝ)*(∑ j, μ.real (firstCrossing b j)) ≤
      ∑ j, μ.real (firstCrossing b j ∩ E) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => gaussian_crossing_endpoint_half_index v b j)
  rw [he,measureReal_iUnion_fintype (firstCrossing_disjoint b) (measurableSet_firstCrossing b)]
  have htail : μ.real E = (gaussianReal 0 (∑ i, v i)).real (Ici b) := gaussian_sum_upper_mass v b
  change (∑ j, μ.real (firstCrossing b j)) ≤ _
  linarith

theorem gaussian_survival_endpoint_lower {n : ℕ} (v : Fin n → NNReal) (c : ℝ) :
    1-2*(gaussianReal 0 (∑ i, v i)).real (Ici c) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  let H : Set (Fin n → ℝ) := {z | ∃ j, c ≤ partialSum z j}
  have hH : MeasurableSet H := by
    change MeasurableSet {z : Fin n → ℝ | ∃ j, c ≤ partialSum z j}
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_le measurable_const
      (HarperPathTransfer.partialSum_measurable j))
  have hs : Hᶜ ⊆ survivalEvent c := by
    intro z hz j
    have hnot : ¬ c ≤ partialSum z j := fun hj => hz ⟨j,hj⟩
    exact (lt_of_not_ge hnot).le
  have h := measureReal_mono (μ := μ) hs (by finiteness)
  rw [measureReal_compl hH,probReal_univ] at h
  have hb := gaussian_maximal_endpoint_bound v c
  change μ.real H ≤ _ at hb
  change _ ≤ μ.real (survivalEvent c)
  linarith

end NField.Alignment.HarperGaussianCrossingEndpoint
