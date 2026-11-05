/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPathTransfer
import NField.Alignment.HarperPrimeBlockJointRelative

/-!
# Upper partial-sum transfer for the actual weighted source blocks

The critical-line weighted block path is bounded by twice the probability
of the comparison Gaussian path with both boundaries enlarged by two.
The first-endpoint threshold is uniform in the number of blocks, their
frequencies and permitted boundaries. Mean centering and Gaussian barrier
estimates are separate obligations.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockPath
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set SteinhausMoment HarperPathGrid
  HarperPathTransfer HarperPrimeBlocks HarperPrimeBlockLaw HarperPrimeBlockGaussian
  HarperPrimeBlockJointLaw HarperPrimeBlockJointRelative HarperPrimeBlockVariance
  HarperTiltedMeasure HarperEulerIntegral HarperPrimeRangeCharacteristic

def blockPathEvent {n : ℕ} (x : ℝ) (l : Fin n → ℕ) (t u v : Fin n → ℝ) : Set PhaseSpace :=
  (fun ω i => blockLog x (l i) (t i) ω) ⁻¹' pathEvent u v

theorem blockPathEvent_measurable {n : ℕ} (x : ℝ) (l : Fin n → ℕ)
    (t u v : Fin n → ℝ) : MeasurableSet (blockPathEvent x l t u v) :=
  (pathEvent_measurable u v).preimage
    (measurable_pi_lambda _ (fun i => blockLog_measurable x (l i) (t i)))

theorem source_radius_monotone {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) :
    Monotone (fun i => Real.sqrt (Real.log (blockUpper x (l i)))/80) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact Real.log_le_log (by linarith [blockUpper_gt_one hx (l i)])
    (blockUpper_antitone hx.le (hl.antitone hij))

theorem source_selected_start_bound {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) {u v : Fin (n+1) → ℝ}
    (hu : ∀ i, -Real.sqrt (Real.log (blockUpper x (l i)))/80 ≤ u i)
    (hv : ∀ i, v i ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80)
    {k : Fin (n+1) → ℤ} (hk : k ∈ selectedCells u v) (i : Fin (n+1)) :
    |gridStart k i| ≤ Real.sqrt (Real.log (blockUpper x (l i)))/40+2 := by
  have h := selected_gridStart_abs_le
    (fun i => div_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 80))
    (source_radius_monotone hx hl) (fun i => by simpa only [neg_div] using hu i) hv hk i
  linarith

theorem blockNormal_nullSingletonClass {x : ℝ} (hx : 0 ≤ x) (l : ℕ) (t : ℝ)
    (hv : 0 < blockVariance (blockUpper x l)) : NullSingletonClass (blockNormal x l t) := by
  unfold blockNormal
  apply ProbabilityTheory.nullSingletonClass_gaussianReal
  have hp : 0 < rangeVariance (primeBlock x l) := by rwa [source_blockVariance hx]
  have hvn : 0 < blockNormalVariance x l := hp
  exact ne_of_gt hvn

theorem normalProduct_closed_eq_halfOpen {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (l : Fin n → ℕ) (t a b : Fin n → ℝ)
    (hv : ∀ i, 0 < blockVariance (blockUpper x (l i))) :
    (normalProductLaw x l t).real (Set.univ.pi (fun i => Icc (a i) (b i))) =
      (normalProductLaw x l t).real (Set.univ.pi (fun i => Ico (a i) (b i))) := by
  rw [normalProductLaw_rectangle,normalProductLaw_rectangle]
  apply Finset.prod_congr rfl
  intro i _
  letI := blockNormal_nullSingletonClass hx (l i) (t i) (hv i)
  exact (measureReal_congr Ico_ae_eq_Icc).symm

theorem eventual_joint_rectangle_upper :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t a : Fin (n+1) → ℝ),
        (∀ i, |a i| ≤ Real.sqrt (Real.log (blockUpper x (l i)))/40+2) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
          (jointBlockEvent x l t (fun i => Icc (a i) (a i+width i))) ≤
        2*(normalProductLaw x l t).real
          (Set.univ.pi (fun i => Ico (a i) (a i+width i))) := by
  obtain ⟨A,hA⟩ := actual_joint_relative_interval_error
  have hs : Tendsto (fun X : ℝ => jointComparisonConstant*X^(-(1/100 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul
      jointComparisonConstant
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    (hs.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨D,hD⟩ := eventually_atTop.mp eventual_blockVariance_bounds
  refine ⟨max A (max B D),fun x hx n l hl hfirst t a ha => ?_⟩
  have ha0 : A ≤ blockUpper x (l 0) := (le_max_left _ _).trans hfirst
  have hb0 : B ≤ blockUpper x (l 0) :=
    (le_max_left B D).trans ((le_max_right _ _).trans hfirst)
  have hd0 : D ≤ blockUpper x (l 0) :=
    (le_max_right B D).trans ((le_max_right _ _).trans hfirst)
  have hv (i : Fin (n+1)) : 0 < blockVariance (blockUpper x (l i)) := by
    have hi := (hD _ (hd0.trans (blockUpper_antitone hx.le (hl.antitone (Fin.zero_le i))))).1
    linarith
  have h := hA x hx n l hl ha0 t a ha
  dsimp only at h
  have hr := (le_abs_self _).trans h.2
  have hsmall := (hB _ hb0).le
  have hratio :
      (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
        (jointBlockEvent x l t (fun i => Icc (a i) (a i+width i)))/
        (normalProductLaw x l t).real
          (Set.univ.pi (fun i => Icc (a i) (a i+width i))) ≤ 2 := by
    dsimp only [width]
    linarith
  have hmul := (div_le_iff₀ h.1).mp hratio
  change _ ≤ 2*(normalProductLaw x l t).real
    (Set.univ.pi (fun i => Ico (a i) (a i+width i)))
  rw [← normalProduct_closed_eq_halfOpen (by linarith : 0 ≤ x) l t a
    (fun i => a i+width i) hv]
  exact hmul

theorem actual_upper_path_transfer :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t u v : Fin (n+1) → ℝ),
        (∀ i, -Real.sqrt (Real.log (blockUpper x (l i)))/80 ≤ u i) →
        (∀ i, v i ≤ Real.sqrt (Real.log (blockUpper x (l i)))/80) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (blockPathEvent x l t u v) ≤
          2*(normalProductLaw x l t).real (pathEvent (fun j => u j-2) (fun j => v j+2)) := by
  obtain ⟨X₀,hX₀⟩ := eventual_joint_rectangle_upper
  refine ⟨X₀,fun x hx n l hl hfirst t u v hu hv => ?_⟩
  let μ := tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)
  let ν := normalProductLaw x l t
  let f := fun ω i => blockLog x (l i) (t i) ω
  letI : IsProbabilityMeasure μ := tiltedMeasure_probability _ (by norm_num [linePoint])
  letI : IsProbabilityMeasure ν := normalProductLaw_probability x l t
  have hrect (k : Fin (n+1) → ℤ) (hk : k ∈ selectedCells u v) :
      μ (f ⁻¹' closedGridCell k) ≤ (2 : ℝ≥0∞)*ν (gridCell k) := by
    have hh := hX₀ x hx n l hl hfirst t (gridStart k)
      (source_selected_start_bound hx hl hu hv hk)
    have he : f ⁻¹' closedGridCell k =
        jointBlockEvent x l t (fun i => Icc (gridStart k i) (gridStart k i+width i)) := by
      ext ω
      simp only [f,closedGridCell,jointBlockEvent,Set.mem_preimage,Set.mem_pi,
        Set.mem_univ,forall_const,Set.mem_setOf_eq,Set.mem_Icc]
    have hh' : μ.real (f ⁻¹' closedGridCell k) ≤ 2*ν.real (gridCell k) := by
      rw [he]
      exact hh
    have hen := ENNReal.ofReal_le_ofReal hh'
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ofReal_measureReal (show μ (f ⁻¹' closedGridCell k) ≠ ⊤ by finiteness),
      ofReal_measureReal (show ν (gridCell k) ≠ ⊤ by finiteness)] at hen
    simpa only [ENNReal.ofReal_ofNat] using hen
  have h := path_probability_transfer μ ν f u v 2 hrect
  have hr := ENNReal.toReal_mono (show (2 : ℝ≥0∞)*ν
    (pathEvent (fun j => u j-2) (fun j => v j+2)) ≠ ⊤ by finiteness) h
  simpa only [μ,ν,f,measureReal_def,blockPathEvent,ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] using hr

end NField.Alignment.HarperPrimeBlockPath
