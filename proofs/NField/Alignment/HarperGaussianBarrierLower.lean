/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianCrossingEndpoint
import NField.Alignment.HarperGaussianCentralLower

/-!
# Two-sided Gaussian constant-barrier estimates

The discrete crossing-to-endpoint bound and a positive interval density
give survival from below. Together with the proved upper estimate this
gives the truncated inverse-square-root scale, with unequal variances.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianBarrierLower
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperGaussianCrossingEndpoint
  HarperGaussianCentralLower HarperGaussianBarrier HarperSourceKilledPath
  HarperCenteredPath HarperPrimeBlocks HarperPrimeBlockGaussian

def barrierLowerConstant : ℝ := 2*intervalLowerConstant

theorem barrierLowerConstant_pos : 0 < barrierLowerConstant := by
  exact mul_pos (by norm_num) intervalLowerConstant_pos

theorem gaussian_survival_interval_lower {n : ℕ} (v : Fin n → NNReal)
    (hv : 0 < ∑ i, v i) {c : ℝ} (hc : 0 < c) :
    2*(gaussianReal 0 (∑ i, v i)).real (Ioo 0 c) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) := by
  have htail := gaussian_positive_interval_tail hv hc
  have hsurv := gaussian_survival_endpoint_lower v c
  linarith

theorem gaussian_constant_barrier_lower {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    barrierLowerConstant*min 1 (c/Real.sqrt (n : ℝ)) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) := by
  by_cases hc0 : c = 0
  · subst c
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : (n : ℝ)/4 ≤ (∑ i, v i : NNReal) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (hv i).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      NNReal.coe_sum,div_eq_mul_inv,one_mul] using h
  have hu : ((∑ i, v i : NNReal) : ℝ) ≤ n := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (hv i).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      NNReal.coe_sum,mul_one] using h
  have hV : (0 : ℝ) < (∑ i, v i : NNReal) := by linarith
  have hi := gaussian_positive_interval_lower hn0 hl hu hc
  have hs := gaussian_survival_interval_lower v (show 0 < ∑ i, v i from hV)
    (lt_of_le_of_ne hc (Ne.symm hc0))
  unfold barrierLowerConstant
  linarith

theorem gaussian_constant_barrier_two_sided {n : ℕ} (hn : 0 < n) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) {c : ℝ} (hc : 1 ≤ c) :
    barrierLowerConstant*min 1 (c/Real.sqrt (n : ℝ)) ≤
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ∧
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      1800*min 1 (c/Real.sqrt (n : ℝ)) := by
  refine ⟨gaussian_constant_barrier_lower hn v hv (by linarith),?_⟩
  by_cases h : c/Real.sqrt (n : ℝ) ≤ 1
  · rw [min_eq_right h]
    have hu := gaussian_constant_barrier_upper hn v (by linarith : 0 ≤ c) hv
    calc
      _ ≤ _ := hu
      _ ≤ 1800*c/Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact measureReal_le_one.trans (by norm_num)

theorem source_constant_barrier_lower :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c : ℝ, 0 ≤ c →
        barrierLowerConstant*min 1 (c/Real.sqrt ((n+1 : ℕ) : ℝ)) ≤
          (centeredNormalProductLaw x l).real (survivalEvent c) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst c hc => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  exact gaussian_constant_barrier_lower (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) (fun i => ⟨(hi i).1,by linarith [(hi i).2]⟩) hc

theorem source_constant_barrier_two_sided :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c : ℝ, 1 ≤ c →
        barrierLowerConstant*min 1 (c/Real.sqrt ((n+1 : ℕ) : ℝ)) ≤
          (centeredNormalProductLaw x l).real (survivalEvent c) ∧
        (centeredNormalProductLaw x l).real (survivalEvent c) ≤
          1800*min 1 (c/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst c hc => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  exact gaussian_constant_barrier_two_sided (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) (fun i => ⟨(hi i).1,by linarith [(hi i).2]⟩) hc

end NField.Alignment.HarperGaussianBarrierLower
