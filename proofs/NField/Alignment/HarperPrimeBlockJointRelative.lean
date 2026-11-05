/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRelativeProducts
import NField.Alignment.HarperPrimeBlockJointLaw
import NField.Alignment.HarperPrimeBlockRelative

/-!
# Uniform joint relative Gaussian comparison for the source blocks

Both joint probabilities are literal measures of the full finite event.
The comparison measure is the independent product of actual normal laws.
Exact independence, positive normal interval masses and geometric error
accumulation give one universal relative bound, independent of the number
of blocks. The partial-sum barrier and low-moment estimate remain separate.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockJointRelative
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set HarperPrimeBlocks HarperPrimeBlockLaw
  HarperPrimeBlockGaussian HarperPrimeBlockRelative HarperPrimeBlockJointLaw
  HarperRelativeProducts HarperGaussianInterval HarperTiltedMeasure HarperEulerIntegral

def jointComparisonConstant : ℝ := 4*intervalComparisonConstant

theorem jointComparisonConstant_pos : 0 < jointComparisonConstant :=
  mul_pos (by norm_num) intervalComparisonConstant_pos

theorem actual_joint_relative_interval_error :
    ∃ X₀ : ℝ, ∀ (x : ℝ), 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) →
      ∀ (t a : Fin (n+1) → ℝ),
        (∀ i, |a i| ≤ Real.sqrt (Real.log (blockUpper x (l i)))/40+2) →
        let I := fun i : Fin (n+1) => Icc (a i) (a i+1/((i.val : ℝ)+1)^2)
        0 < (normalProductLaw x l t).real (Set.univ.pi I) ∧
        |(tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (jointBlockEvent x l t I)/
            (normalProductLaw x l t).real (Set.univ.pi I)-1| ≤
          jointComparisonConstant*(blockUpper x (l 0))^(-(1/100 : ℝ)) := by
  obtain ⟨A,hA⟩ := eventual_source_interval_estimates
  obtain ⟨B,hB⟩ := eventually_atTop.mp eventual_error_sum_scale
  refine ⟨max A B,fun x hx n l hl hfirst t a ha => ?_⟩
  let I := fun i : Fin (n+1) => Icc (a i) (a i+1/((i.val : ℝ)+1)^2)
  have hi (i : Fin (n+1)) :=
    hA x hx n l hl ((le_max_left A B).trans hfirst) i (t i) (a i) (ha i)
  have hscale := hB (blockUpper x (l 0)) ((le_max_right A B).trans hfirst)
  have hsum := reversed_block_error_sum hx hl hscale.1
  have hpositive (i : Fin (n+1)) : 0 < (blockNormal x (l i) (t i)).real (I i) :=
    (Real.rpow_pos_of_pos (by linarith [blockUpper_gt_one hx (l i)]) _).trans_le (hi i).1
  have hproduct := finite_relative_product_error Finset.univ
    (fun i : Fin (n+1) => (blockLaw x (l i) (t i)).real (I i))
    (fun i => (blockNormal x (l i) (t i)).real (I i))
    (fun i => intervalComparisonConstant*(blockUpper x (l i))^(-(1/100 : ℝ)))
    (fun i _ => mul_nonneg intervalComparisonConstant_pos.le
      (Real.rpow_nonneg (by linarith [blockUpper_gt_one hx (l i)]) _))
    (fun i _ => (hi i).2) (hsum.trans hscale.2)
  change 0 < (normalProductLaw x l t).real (Set.univ.pi I) ∧
    |(tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (jointBlockEvent x l t I)/
      (normalProductLaw x l t).real (Set.univ.pi I)-1| ≤ _
  rw [normalProductLaw_rectangle,
    jointBlockEvent_probability hx.le l hl.injective t I (fun _ => measurableSet_Icc)]
  refine ⟨Finset.prod_pos (fun i _ => hpositive i),?_⟩
  calc
    _ ≤ 2*∑ i : Fin (n+1), intervalComparisonConstant*
        (blockUpper x (l i))^(-(1/100 : ℝ)) := hproduct
    _ ≤ 2*(2*intervalComparisonConstant*(blockUpper x (l 0))^(-(1/100 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by unfold jointComparisonConstant; ring

end NField.Alignment.HarperPrimeBlockJointRelative
