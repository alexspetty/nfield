/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianIntervalLower
import NField.Alignment.HarperPrimeBlockGrowth
import NField.Alignment.HarperPrimeBlockGaussian

/-!
# Relative Gaussian interval comparison for the actual source blocks

The normal mass lower bound and absolute approximation combine to give
relative error O(X^(-1/100)). Along each finite reversed block sequence,
the literal one-based source widths satisfy the required lower bound.
The final theorem discharges all cutoff, variance and width conditions
using one universal threshold on the first block. Joint interval events
and the partial-sum probability barrier are not asserted here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockRelative
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set HarperPrimeBlocks HarperPrimeBlockLaw
  HarperPrimeRangeCharacteristic HarperPrimeBlockVariance HarperGaussianInterval
  HarperGaussianIntervalLower HarperPrimeBlockGrowth HarperPrimeBlockGaussian
  HarperEulerIntegral HarperTiltedMeasure

theorem relative_error_of_absolute {A B C X : ℝ} (hX : 0 < X) (hC : 0 ≤ C)
    (hB : X^(-(1/150 : ℝ)) ≤ B) (herror : |A-B| ≤ C*X^(-(1/60 : ℝ))) :
    |A/B-1| ≤ C*X^(-(1/100 : ℝ)) := by
  have hp := Real.rpow_pos_of_pos hX (-(1/150 : ℝ))
  have hB0 := hp.trans_le hB
  have hid : A/B-1 = (A-B)/B := by field_simp
  rw [hid, abs_div, abs_of_pos hB0]
  calc
    _ ≤ (C*X^(-(1/60 : ℝ)))/B := div_le_div_of_nonneg_right herror hB0.le
    _ ≤ (C*X^(-(1/60 : ℝ)))/X^(-(1/150 : ℝ)) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg hX.le _)) hp hB
    _ = _ := by rw [mul_div_assoc, ← Real.rpow_sub hX]; norm_num

theorem blockNormal_interval_mass_lower {x : ℝ} (hx : 1 < x) (l : ℕ)
    (hlog : 360000 ≤ Real.log (blockUpper x l))
    (hvlo : (1/4 : ℝ) ≤ blockVariance (blockUpper x l))
    (hvhi : blockVariance (blockUpper x l) ≤ 3/4)
    (t a w : ℝ) (ha : |a| ≤ Real.sqrt (Real.log (blockUpper x l))/40+2)
    (hw : (blockUpper x l)^(-(1/300 : ℝ)) ≤ w) (hw1 : w ≤ 1) :
    (blockUpper x l)^(-(1/150 : ℝ)) ≤
      (blockNormal x l t).real (Icc a (a+w)) := by
  have hx0 : 0 ≤ x := by linarith
  have hvlo' : (1/4 : ℝ) ≤ rangeVariance (primeBlock x l) := by
    rwa [source_blockVariance hx0]
  have hvhi' : rangeVariance (primeBlock x l) ≤ 3/4 := by
    rwa [source_blockVariance hx0]
  have hm : |rangeMean (primeBlock x l) (fun _ => t)| ≤ 3/2 :=
    (rangeMean_abs_le _ _).trans (by linarith)
  unfold blockNormal
  exact gaussian_interval_mass_lower (by linarith [blockUpper_gt_one hx l])
    hlog (v := blockNormalVariance x l) hvlo' hvhi' hm ha hw hw1

theorem eventual_source_interval_estimates :
    ∃ X₀ : ℝ, ∀ (x : ℝ), 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) →
      ∀ (i : Fin (n+1)) (t a : ℝ),
        |a| ≤ Real.sqrt (Real.log (blockUpper x (l i)))/40+2 →
        let I := Icc a (a+1/((i.val : ℝ)+1)^2)
        (blockUpper x (l i))^(-(1/150 : ℝ)) ≤ (blockNormal x (l i) t).real I ∧
        |(blockLaw x (l i) t).real I/(blockNormal x (l i) t).real I-1| ≤
          intervalComparisonConstant*(blockUpper x (l i))^(-(1/100 : ℝ)) := by
  obtain ⟨V,hV⟩ := eventually_atTop.mp eventual_blockVariance_bounds
  obtain ⟨A,hA⟩ := eventual_block_interval_error
  refine ⟨max A (max V (Real.exp 360000)),fun x hx n l hl hfirst i t a ha => ?_⟩
  have hi : blockUpper x (l 0) ≤ blockUpper x (l i) :=
    blockUpper_antitone hx.le (hl.antitone (Fin.zero_le i))
  have hAi : A ≤ blockUpper x (l i) := (le_max_left _ _).trans (hfirst.trans hi)
  have hVi : V ≤ blockUpper x (l i) :=
    (le_max_left V _).trans ((le_max_right A _).trans (hfirst.trans hi))
  have hlog0 : 360000 ≤ Real.log (blockUpper x (l 0)) := by
    have he : Real.exp 360000 ≤ blockUpper x (l 0) :=
      (le_max_right V _).trans ((le_max_right A _).trans hfirst)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hlogi := hlog0.trans (reversed_block_log_ge hx hl i)
  have hw := reversed_block_width_lower hx hl (by linarith : 600 ≤ Real.log (blockUpper x (l 0))) i
  have hw1 := reciprocal_square_width_le_one
    (by exact le_add_of_nonneg_left (Nat.cast_nonneg _) : 1 ≤ (i.val : ℝ)+1)
  have hv := hV (blockUpper x (l i)) hVi
  have hmass := blockNormal_interval_mass_lower hx (l i) hlogi hv.1 hv.2 t a _ ha hw hw1
  dsimp only
  refine ⟨hmass,relative_error_of_absolute (by linarith [blockUpper_gt_one hx (l i)])
    intervalComparisonConstant_pos.le hmass ?_⟩
  exact hA x hx (l i) hAi t a _ (by linarith)

theorem actual_weighted_relative_interval_error :
    ∃ X₀ : ℝ, ∀ (x : ℝ), 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) →
      ∀ (i : Fin (n+1)) (t a : ℝ),
        |a| ≤ Real.sqrt (Real.log (blockUpper x (l i)))/40+2 →
        |(tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
            {ω | blockLog x (l i) t ω ∈ Icc a (a+1/((i.val : ℝ)+1)^2)}/
            (blockNormal x (l i) t).real (Icc a (a+1/((i.val : ℝ)+1)^2))-1| ≤
          intervalComparisonConstant*(blockUpper x (l i))^(-(1/100 : ℝ)) := by
  obtain ⟨X₀,h⟩ := eventual_source_interval_estimates
  refine ⟨X₀,fun x hx n l hl hfirst i t a ha => ?_⟩
  simpa only [blockLaw_interval] using (h x hx n l hl hfirst i t a ha).2

end NField.Alignment.HarperPrimeBlockRelative
