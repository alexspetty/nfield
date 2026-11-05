/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMeanDrift

/-!
# Centering the actual Gaussian comparison path

Coordinatewise subtraction maps the comparison normal product exactly to
the centered normal product, preserving its variances. The cumulative
leading-mean drift gives an upper path comparison with one fixed boundary
allowance, before any Gaussian barrier theorem is used.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperCenteredPath
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set HarperPrimeBlocks HarperPrimeRangeCharacteristic
  HarperPrimeBlockGaussian HarperPrimeBlockJointLaw HarperPrimeBlockPath HarperPathGrid
  HarperPathTransfer HarperMeanDrift HarperTiltedMeasure HarperEulerIntegral

def centeredNormalProductLaw {n : ℕ} (x : ℝ) (l : Fin n → ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal 0 (blockNormalVariance x (l i)))

def centeredPathAllowance : ℝ := cumulativeMeanConstant+2

theorem centeredPathAllowance_pos : 0 < centeredPathAllowance := by
  unfold centeredPathAllowance
  linarith [cumulativeMeanConstant_pos]

theorem centeredNormalProduct_probability {n : ℕ} (x : ℝ) (l : Fin n → ℕ) :
    IsProbabilityMeasure (centeredNormalProductLaw x l) := by
  unfold centeredNormalProductLaw
  infer_instance

theorem gaussian_product_center_map {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ι → NNReal) :
    (Measure.pi (fun i => gaussianReal (m i) (v i))).map (fun z i => z i-m i) =
      Measure.pi (fun i => gaussianReal 0 (v i)) := by
  let f := fun i : ι => fun z : ℝ => z-m i
  letI (i : ι) : IsProbabilityMeasure ((gaussianReal (m i) (v i)).map (f i)) :=
    Measure.isProbabilityMeasure_map ((measurable_id.sub_const (m i)).aemeasurable)
  have h := Measure.pi_map_pi (μ := fun i => gaussianReal (m i) (v i))
    (f := f) (fun i => (measurable_id.sub_const (m i)).aemeasurable)
  simpa only [f,gaussianReal_map_sub_const,sub_self] using h

theorem normalProduct_center_map {n : ℕ} (x : ℝ) (l : Fin n → ℕ) (t : Fin n → ℝ) :
    (normalProductLaw x l t).map
      (fun z i => z i-rangeMean (primeBlock x (l i)) (fun _ => t i)) =
      centeredNormalProductLaw x l :=
  gaussian_product_center_map _ _

theorem partialSum_sub {n : ℕ} (z m : Fin n → ℝ) (j : Fin n) :
    partialSum (fun i => z i-m i) j = partialSum z j-partialSum m j := by
  simp only [partialSum,Finset.sum_sub_distrib]

theorem normalProduct_path_centering {n : ℕ} (x : ℝ) (l : Fin n → ℕ)
    (t u v : Fin n → ℝ) :
    (normalProductLaw x l t).real (pathEvent u v) =
      (centeredNormalProductLaw x l).real (pathEvent
        (fun j => u j-partialSum (fun i => rangeMean (primeBlock x (l i)) (fun _ => t i)) j)
        (fun j => v j-partialSum (fun i => rangeMean (primeBlock x (l i)) (fun _ => t i)) j)) := by
  let m := fun i => rangeMean (primeBlock x (l i)) (fun _ => t i)
  have hm : Measurable (fun z : Fin n → ℝ => fun i => z i-m i) := by fun_prop
  have he : (fun z : Fin n → ℝ => fun i => z i-m i) ⁻¹'
      pathEvent (fun j => u j-partialSum m j) (fun j => v j-partialSum m j) =
      pathEvent u v := by
    ext z
    simp only [Set.mem_preimage,pathEvent,Set.mem_setOf_eq,partialSum_sub,
      sub_le_sub_iff_right]
  simp only [measureReal_def]
  rw [← normalProduct_center_map x l t,
    Measure.map_apply hm (pathEvent_measurable _ _),he]

theorem actual_centered_upper_path_transfer :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t u v : Fin (n+1) → ℝ),
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        (∀ i, -Real.sqrt (Real.log (blockUpper x (l i)))/80 ≤ u i) →
        (∀ i, v i ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (blockPathEvent x l t u v) ≤
          2*(centeredNormalProductLaw x l).real (pathEvent
            (fun j => u j-((j.val : ℝ)+1)-centeredPathAllowance)
            (fun j => v j-((j.val : ℝ)+1)+centeredPathAllowance)) := by
  obtain ⟨A,hA⟩ := actual_upper_path_transfer
  obtain ⟨B,hB⟩ := source_cumulative_mean_error
  refine ⟨max A B,fun x hx n l hl hfirst t u v ht hu hv => ?_⟩
  have hpath := hA x hx n l hl ((le_max_left _ _).trans hfirst) t u v hu hv
  have hmean := hB x hx n l hl ((le_max_right _ _).trans hfirst) t ht
  rw [normalProduct_path_centering] at hpath
  letI := centeredNormalProduct_probability x l
  apply hpath.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine measureReal_mono ?_ (by finiteness)
  intro z hz j
  have hzj := hz j
  have hm := abs_le.mp (hmean j)
  unfold centeredPathAllowance
  exact ⟨by linarith,by linarith⟩

end NField.Alignment.HarperCenteredPath
