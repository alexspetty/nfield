/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianEndpointLaw
import NField.Alignment.HarperGaussianPathSplit

/-!
# The Gaussian half-time survival contraction

The proved finite-path deficit bound controls a large prefix deficit;
the independent Gaussian suffix endpoint controls the other case. All
probabilities refer to the actual finite products, with unequal variances.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianSurvivalContraction
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperGaussianKilledPath
  HarperGaussianEndpointLaw HarperGaussianPathSplit HarperCenteredPath
  HarperSourceKilledPath HarperPrimeBlocks HarperPrimeBlockGaussian

theorem gaussian_survival_contraction {m n : ℕ} (hn : 0 < n)
    (v : Fin (m+n) → NNReal) {c : ℝ} (hc : 0 ≤ c)
    (hpre : ∀ i : Fin m, 0 < v (Fin.castAdd n i) ∧ (v (Fin.castAdd n i) : ℝ) ≤ 1)
    (hsuf : ∀ i : Fin n, (1/4 : ℝ) ≤ v (Fin.natAdd m i)) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      (c+2)/(Real.sqrt (n : ℝ)/20+2) +
        (3/5)*(Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real
          (survivalEvent c) := by
  have h := gaussian_survival_split v hc (Real.sqrt (n : ℝ)/20)
  have hlarge := gaussian_survival_deficit_tail hc
    (show 0 ≤ Real.sqrt (n : ℝ)/20 by positivity)
    (fun i => v (Fin.castAdd n i)) (fun i => (hpre i).1) (fun i => (hpre i).2)
  have hend := gaussian_sum_endpoint_contraction hn (fun i => v (Fin.natAdd m i)) hsuf
  have hmul := mul_le_mul_of_nonneg_left hend
    (show 0 ≤ (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real
      (survivalEvent c) from measureReal_nonneg)
  nlinarith

theorem gaussian_half_survival_contraction {m : ℕ} (hm : 0 < m)
    (v : Fin (m+m) → NNReal) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      (c+2)/(Real.sqrt (m : ℝ)/20+2) +
        (3/5)*(Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd m i)))).real
          (survivalEvent c) := by
  apply gaussian_survival_contraction hm v hc
  · intro i
    refine ⟨?_,(hv _).2⟩
    change (0 : ℝ) < v (Fin.castAdd m i)
    linarith [(hv (Fin.castAdd m i)).1]
  · intro i
    exact (hv _).1

theorem gaussian_half_survival_recurrence {m : ℕ} (hm : 0 < m)
    (v : Fin (m+m) → NNReal) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      20*(c+2)/Real.sqrt (m : ℝ) +
        (3/5)*(Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd m i)))).real
          (survivalEvent c) := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have h := div_le_div_of_nonneg_left (by linarith : 0 ≤ c+2)
    (by positivity : 0 < Real.sqrt (m : ℝ)/20)
    (by linarith : Real.sqrt (m : ℝ)/20 ≤ Real.sqrt (m : ℝ)/20+2)
  have he : (c+2)/(Real.sqrt (m : ℝ)/20) = 20*(c+2)/Real.sqrt (m : ℝ) := by
    field_simp
  rw [he] at h
  linarith [gaussian_half_survival_contraction hm v hc hv]

theorem source_half_survival_recurrence :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (m : ℕ) (l : Fin ((m+1)+(m+1)) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c : ℝ, 0 ≤ c →
        (centeredNormalProductLaw x l).real (survivalEvent c) ≤
          20*(c+2)/Real.sqrt ((m+1 : ℕ) : ℝ) +
            (3/5)*(centeredNormalProductLaw x
              (fun i : Fin (m+1) => l (Fin.castAdd (m+1) i))).real (survivalEvent c) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx m l hl hfirst c hc => ?_⟩
  have hi := hX₀ x hx ((m+1)+m) l hl hfirst
  apply gaussian_half_survival_recurrence (by omega : 0 < m+1)
    (fun i => blockNormalVariance x (l i)) hc
  intro i
  exact ⟨(hi i).1,by linarith [(hi i).2]⟩

end NField.Alignment.HarperGaussianSurvivalContraction
