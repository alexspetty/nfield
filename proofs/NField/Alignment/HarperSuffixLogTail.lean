/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSuffixIntegrability

/-!
# Two-sided logarithmic tails of the actual suffix products

The positive and inverse second moments control both signs of the
logarithm under the original Haar law. The source allowance is preserved
literally, including its squared logarithmic factor after exponentiation.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSuffixLogTail
open scoped BigOperators
open MeasureTheory Set Filter SteinhausMoment HarperPrimeBlocks HarperFrequencyMesh
  HarperCriticalGoodEvent HarperSuffixSecondMoments HarperSuffixIntegrability
  HarperSmoothCount HarperSmoothDivisor CollisionMertensInput

theorem norm_log_tail_subset (f : PhaseSpace → ℂ) (hf : ∀ ω, f ω ≠ 0) (A : ℝ) :
    {ω | A < |Real.log ‖f ω‖|} ⊆
      {ω | Real.exp (2*A) ≤ ‖f ω‖^2} ∪ {ω | Real.exp (2*A) ≤ ‖(f ω)⁻¹‖^2} := by
  intro ω hω
  change A < |Real.log ‖f ω‖| at hω
  have hp : 0 < ‖f ω‖ := norm_pos_iff.mpr (hf ω)
  have he : Real.exp (2*A) = (Real.exp A)^2 := by
    rw [show 2*A=A+A by ring,Real.exp_add,pow_two]
  rcases lt_abs.mp hω with h | h
  · left
    rw [he]
    have hh : Real.exp A ≤ ‖f ω‖ := by
      simpa only [Real.exp_log hp] using (Real.exp_le_exp.mpr h.le)
    exact pow_le_pow_left₀ (Real.exp_pos _).le hh 2
  · right
    rw [he]
    have hh : Real.exp A ≤ ‖(f ω)⁻¹‖ := by
      rw [norm_inv]
      have hh := Real.exp_le_exp.mpr h.le
      simpa only [Real.exp_neg,Real.exp_log hp] using hh
    exact pow_le_pow_left₀ (Real.exp_pos _).le hh 2

theorem suffix_log_tail_normalizer {x : ℝ} (hx : 1 ≤ x) (M : ℕ) (t : ℝ) (j : ℕ) (A : ℝ) :
    phaseMeasure.real {ω | A < |suffixLog x M t j ω|} ≤
      2*inversePrimeProduct (blockUpper x j)/Real.exp (2*A) := by
  have hsub : {ω | A < |suffixLog x M t j ω|} ⊆
      {ω | Real.exp (2*A) ≤ ‖suffixProduct x M t j ω‖^2} ∪
      {ω | Real.exp (2*A) ≤ ‖(suffixProduct x M t j ω)⁻¹‖^2} := by
    simpa only [suffixLog_eq_log_norm] using
      norm_log_tail_subset (suffixProduct x M t j) (suffixProduct_ne_zero x M t j) A
  have hm := (measureReal_mono (μ := phaseMeasure) hsub (by finiteness)).trans (measureReal_union_le _ _)
  have hpos := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _))
    (suffix_positive_integrable x M t j) (Real.exp (2*A))).trans (suffix_positive_moment_le hx M t j)
  have hneg := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _))
    (suffix_inverse_integrable x M t j) (Real.exp (2*A))).trans (suffix_inverse_moment_le hx M t j)
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  have ht := mul_le_mul_of_nonneg_left hm (Real.exp_pos (2*A)).le
  nlinarith

theorem suffix_normalizer_log_bound :
    ∃ X₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ M : ℕ,
      X₀ ≤ blockUpper x M → ∀ j ≤ M,
      inversePrimeProduct (blockUpper x j) ≤ C*logScale x j := by
  obtain ⟨C,hC,hbound⟩ := inversePrimeProduct_isBigO_log.exists_pos
  obtain ⟨P₀,hP₀⟩ := eventually_atTop.mp hbound.bound
  refine ⟨max P₀ 1,C,hC,fun x hx M hM j hj => ?_⟩
  have hP := (le_max_left _ _).trans (hM.trans (blockUpper_antitone hx.le hj))
  have h := hP₀ _ hP
  simpa only [Real.norm_eq_abs,abs_of_pos (inversePrimeProduct_pos _),
    abs_of_nonneg (Real.log_nonneg (blockUpper_gt_one hx j).le),logScale] using h

theorem suffix_source_tail :
    ∃ X₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ M : ℕ,
      X₀ ≤ blockUpper x M → ∀ j ≤ M, ∀ a t : ℝ,
      phaseMeasure.real {ω | sourceAllowance x a j < |suffixLog x M t j ω|} ≤
        C*Real.exp (-2*a)/(logScale x j*(Real.log (logScale x j))^4) := by
  obtain ⟨X₀,C,hC,hbound⟩ := suffix_normalizer_log_bound
  refine ⟨max X₀ (Real.exp (Real.exp 2)),2*C,by positivity,fun x hx M hM j hj a t => ?_⟩
  have hLj : Real.exp 2 ≤ logScale x j := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 2))
      ((le_max_right _ _).trans (hM.trans (blockUpper_antitone hx.le hj)))
    simpa only [Real.log_exp,logScale] using h
  have hL : 1 < logScale x j := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)) hLj
  have hp := hbound x hx M ((le_max_left _ _).trans hM) j hj
  calc
    _ ≤ 2*inversePrimeProduct (blockUpper x j)/Real.exp (2*sourceAllowance x a j) :=
      suffix_log_tail_normalizer hx.le M t j _
    _ ≤ 2*(C*logScale x j)/Real.exp (2*sourceAllowance x a j) := by
      gcongr
    _ = _ := by
      rw [show 2*sourceAllowance x a j=sourceAllowance x a j+sourceAllowance x a j by ring,
        Real.exp_add,exp_sourceAllowance a j hL]
      have he : Real.exp (-2*a) = (Real.exp a*Real.exp a)⁻¹ := by
        rw [show -2*a=-(a+a) by ring,Real.exp_neg,Real.exp_add]
      rw [he]
      have hL0 : logScale x j ≠ 0 := by linarith
      have hl0 : Real.log (logScale x j) ≠ 0 := ne_of_gt (Real.log_pos hL)
      have ha0 := ne_of_gt (Real.exp_pos a)
      field_simp

end NField.Alignment.HarperSuffixLogTail
