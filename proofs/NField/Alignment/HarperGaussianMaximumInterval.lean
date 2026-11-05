/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianFirstCrossing

/-!
# A uniform interval bound for the Gaussian path maximum

Early first crossings are disjoint and leave a long surviving suffix.
The late maximum has a Gaussian prefix endpoint independent of the suffix.
Combining the two estimates handles every positive path length and every
interval location, with unequal coordinate variances in [1/4,1].
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianMaximumInterval
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperPathMaximum HarperFirstCrossing
  HarperGaussianFirstCrossing HarperGaussianLateMaximum HarperGaussianBarrier
  HarperCenteredPath HarperSourceKilledPath HarperPrimeBlocks HarperPrimeBlockGaussian

theorem gaussian_early_crossing_bound {m n : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (v : Fin (m+n) → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (j : Fin (m+n)) (hj : j ∈ earlyIndices m n) (b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (maximumWindow b c ∩ firstCrossing b j) ≤
      (2700*c/Real.sqrt ((m+n : ℕ) : ℝ))*
        (Measure.pi (fun i => gaussianReal 0 (v i))).real (firstCrossing b j) := by
  have hjm : j.val < m := (Finset.mem_filter.mp hj).2
  let q := (m+n)-(j.val+1)
  have hnq : n ≤ q := by dsimp [q]; omega
  have hq : 0 < q := hn.trans_le hnq
  have hN : m+n = (j.val+1)+q := by dsimp [q]; omega
  have hbase := gaussian_crossing_window_index hN hq v hv j rfl b (by linarith : 0 ≤ c)
  have hsQ : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hsN : 0 < Real.sqrt ((m+n : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < m+n by omega))
  have hs : Real.sqrt ((m+n : ℕ) : ℝ) ≤ (3/2)*Real.sqrt (q : ℝ) := by
    apply sqrt_double_le_three_halves (by positivity) (by positivity)
    exact_mod_cast (show m+n ≤ 2*q by omega)
  have hcoef : 900*(c+1)/Real.sqrt (q : ℝ) ≤ 2700*c/Real.sqrt ((m+n : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hsQ hsN).mpr
    have h1 := mul_le_mul_of_nonneg_right (show 900*(c+1) ≤ 1800*c by linarith)
      hsN.le
    have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 1800*c by linarith)
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef measureReal_nonneg)

theorem gaussian_maximum_interval_balanced {m n : ℕ} (hm : 0 < m)
    (hmn : m ≤ n) (hnm : n ≤ m+1) (v : Fin (m+n) → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (maximumWindow b c) ≤
      3000*c/Real.sqrt ((m+n : ℕ) : ℝ) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  have hn : 0 < n := hm.trans_le hmn
  have hsum : (∑ j ∈ earlyIndices m n, μ.real (maximumWindow b c ∩ firstCrossing b j)) ≤
      2700*c/Real.sqrt ((m+n : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ earlyIndices m n,
          (2700*c/Real.sqrt ((m+n : ℕ) : ℝ))*μ.real (firstCrossing b j) :=
        Finset.sum_le_sum (fun j hj => gaussian_early_crossing_bound hn hmn v hv j hj b hc)
      _ = (2700*c/Real.sqrt ((m+n : ℕ) : ℝ))*
          (∑ j ∈ earlyIndices m n, μ.real (firstCrossing b j)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        have h := firstCrossing_mass_sum_le_one μ b (earlyIndices m n)
        have hC : 0 ≤ 2700*c/Real.sqrt ((m+n : ℕ) : ℝ) := by positivity
        nlinarith
  have hlate := gaussian_late_maximum_interval hm hn v (fun i => (hv _).1) b (by linarith : 0 ≤ c)
  have hsM : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsN : 0 < Real.sqrt ((m+n : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < m+n by omega))
  have hs : Real.sqrt ((m+n : ℕ) : ℝ) ≤ 2*Real.sqrt (m : ℝ) := by
    have hnum : ((m+n : ℕ) : ℝ) ≤ 4*(m : ℝ) := by exact_mod_cast (show m+n ≤ 4*m by omega)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ (m+n : ℕ) by positivity)]
  have hcoef : 2*c/Real.sqrt (m : ℝ) ≤ 4*c/Real.sqrt ((m+n : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hsM hsN).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ c by linarith)]
  have hcover := measureReal_mono (μ := μ) (maximumWindow_early_late_cover m n b c) (by finiteness)
  have huni := measureReal_union_le (μ := μ)
    (⋃ j ∈ earlyIndices m n, maximumWindow b c ∩ firstCrossing b j)
    (lateWindow (m := m) (n := n) b c)
  have hfin := measureReal_biUnion_finset_le (μ := μ) (earlyIndices m n)
    (fun j => maximumWindow b c ∩ firstCrossing b j)
  change μ.real (lateWindow (m := m) (n := n) b c) ≤ _ at hlate
  change μ.real (maximumWindow b c) ≤ 3000*c/Real.sqrt ((m+n : ℕ) : ℝ)
  calc
    _ ≤ _ := hcover.trans huni
    _ ≤ 2700*c/Real.sqrt ((m+n : ℕ) : ℝ) + 4*c/Real.sqrt ((m+n : ℕ) : ℝ) :=
      add_le_add (hfin.trans hsum) (hlate.trans hcoef)
    _ = (2700*c+4*c)/Real.sqrt ((m+n : ℕ) : ℝ) := (add_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hsN.le

theorem gaussian_maximum_interval {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (maximumWindow b c) ≤
      3000*c/Real.sqrt (n : ℝ) := by
  by_cases hn1 : n = 1
  · have hs : Real.sqrt (n : ℝ) = 1 := by rw [hn1]; norm_num
    rw [hs,div_one]
    have hp : (Measure.pi (fun i => gaussianReal 0 (v i))).real (maximumWindow b c) ≤ 1 :=
      measureReal_le_one
    linarith
  · have hparts : ∃ m q : ℕ, n = m+q ∧ 0 < m ∧ m ≤ q ∧ q ≤ m+1 := by
      refine ⟨n/2,n-n/2,?_,?_,?_,?_⟩ <;> omega
    obtain ⟨m,q,rfl,hm,hmq,hqm⟩ := hparts
    exact gaussian_maximum_interval_balanced hm hmq hqm v hv b hc

theorem gaussian_pathMaximum_interval {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      {z | pathMaximum hn z ∈ Icc b (b+c)} ≤ 3000*c/Real.sqrt (n : ℝ) := by
  have he : {z | pathMaximum hn z ∈ Icc b (b+c)} = maximumWindow b c := by
    ext z
    exact (mem_maximumWindow_iff hn z b c).symm
  rw [he]
  exact gaussian_maximum_interval hn v hv b hc

theorem source_maximum_interval :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ b c : ℝ, 1 ≤ c →
        (centeredNormalProductLaw x l).real (maximumWindow b c) ≤
          3000*c/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst b c hc => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  apply gaussian_maximum_interval (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) (fun i => ⟨(hi i).1,by linarith [(hi i).2]⟩) b hc

end NField.Alignment.HarperGaussianMaximumInterval
