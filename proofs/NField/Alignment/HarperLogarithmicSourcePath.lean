/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLogarithmicBarrier

/-!
# The logarithmic upper bound for actual weighted block paths

The checked centered comparison and logarithmic Gaussian barrier combine
under one source threshold. Original frequency and boundary restrictions
remain explicit, as do the factor two and fixed centering allowance.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLogarithmicSourcePath
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPrimeBlocks HarperPrimeBlockPath
  HarperCenteredPath HarperLogarithmicBarrier HarperGaussianBarrierPerturbation
  HarperTiltedMeasure HarperEulerIntegral

theorem actual_logarithmic_path_upper :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t u v : Fin (n+1) → ℝ),
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        (∀ i, -Real.sqrt (Real.log (blockUpper x (l i)))/80 ≤ u i) →
        (∀ i, v i ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80) →
        ∀ a : ℝ, 1 ≤ a →
        (∀ j, v j-((j.val : ℝ)+1)+centeredPathAllowance ≤
          a+10*Real.log ((j.val : ℝ)+1)) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (blockPathEvent x l t u v) ≤
          (4*logSurvivalConstant)*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨A,hA⟩ := actual_centered_upper_path_transfer
  obtain ⟨B,hB⟩ := source_logarithmic_barrier_array
  refine ⟨max A B,fun x hx n l hl hfirst t u v ht hu hv a ha hbar => ?_⟩
  have hp := hA x hx n l hl ((le_max_left _ _).trans hfirst) t u v ht hu hv
  have hg := hB x hx n l hl ((le_max_right _ _).trans hfirst) a ha
    (fun j => v j-((j.val : ℝ)+1)+centeredPathAllowance) hbar
  letI := centeredNormalProduct_probability x l
  have hm := measureReal_mono (μ := centeredNormalProductLaw x l)
    (show pathEvent (fun j => u j-((j.val : ℝ)+1)-centeredPathAllowance)
        (fun j => v j-((j.val : ℝ)+1)+centeredPathAllowance) ⊆
      barrierEvent (fun j => v j-((j.val : ℝ)+1)+centeredPathAllowance)
      from fun _ hz j => (hz j).2) (by finiteness)
  calc
    _ ≤ _ := hp
    _ ≤ 2*(centeredNormalProductLaw x l).real
        (barrierEvent (fun j => v j-((j.val : ℝ)+1)+centeredPathAllowance)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ 2*((2*logSurvivalConstant)*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

theorem actual_logarithmic_block_barrier :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t u v : Fin (n+1) → ℝ),
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        (∀ i, -Real.sqrt (Real.log (blockUpper x (l i)))/80 ≤ u i) →
        (∀ i, v i ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80) →
        ∀ a : ℝ, 1 ≤ a →
        (∀ j, v j ≤ ((j.val : ℝ)+1)+a+10*Real.log ((j.val : ℝ)+1)) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (blockPathEvent x l t u v) ≤
          (4*logSurvivalConstant)*min 1
            ((a+centeredPathAllowance)/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := actual_logarithmic_path_upper
  refine ⟨X₀,fun x hx n l hl hfirst t u v ht hu hv a ha hbar => ?_⟩
  exact hX₀ x hx n l hl hfirst t u v ht hu hv (a+centeredPathAllowance)
    (by linarith [centeredPathAllowance_pos]) (fun j => by linarith [hbar j])

end NField.Alignment.HarperLogarithmicSourcePath
