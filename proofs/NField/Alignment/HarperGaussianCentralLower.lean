/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianIntervalMass

/-!
# A positive Gaussian interval lower bound

Comparable variance gives a uniform density lower bound near zero.
Integration over (0,min(c,sqrt(q))) yields the correct truncated scale.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianCentralLower
open MeasureTheory ProbabilityTheory Set HarperGaussianEndpoint

def intervalLowerConstant : ℝ := Real.exp (-2)/Real.sqrt (2*Real.pi)

theorem intervalLowerConstant_pos : 0 < intervalLowerConstant := by
  unfold intervalLowerConstant
  positivity

theorem gaussian_density_lower {q : ℝ} (hq : 0 < q) {v : NNReal}
    (hl : q/4 ≤ (v : ℝ)) (hu : (v : ℝ) ≤ q) {z : ℝ} (hz : z^2 ≤ q) :
    Real.exp (-2)/Real.sqrt (2*Real.pi*q) ≤ gaussianPDFReal 0 v z := by
  have hv : (0 : ℝ) < v := by linarith
  have hexp : (-2 : ℝ) ≤ -(z^2)/(2*(v : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(v : ℝ))).mpr
    linarith
  have hs : 1/Real.sqrt (2*Real.pi*q) ≤ 1/Real.sqrt (2*Real.pi*(v : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  unfold gaussianPDFReal
  simp only [sub_zero]
  calc
    _ = (1/Real.sqrt (2*Real.pi*q))*Real.exp (-2) := by ring
    _ ≤ _ := by
      simpa only [one_div] using mul_le_mul hs (Real.exp_le_exp.mpr hexp)
        (Real.exp_pos (-2)).le (by positivity : 0 ≤ 1/Real.sqrt (2*Real.pi*(v : ℝ)))

theorem gaussian_positive_interval_lower {q : ℝ} (hq : 0 < q) {v : NNReal}
    (hl : q/4 ≤ (v : ℝ)) (hu : (v : ℝ) ≤ q) {c : ℝ} (hc : 0 ≤ c) :
    intervalLowerConstant*min 1 (c/Real.sqrt q) ≤ (gaussianReal 0 v).real (Ioo 0 c) := by
  have hv : (0 : ℝ) < v := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  let R := min c (Real.sqrt q)
  have hR : 0 ≤ R := le_min hc hs.le
  have hRc : R ≤ c := min_le_left _ _
  have hRs : R ≤ Real.sqrt q := min_le_right _ _
  have hr : R/Real.sqrt q = min 1 (c/Real.sqrt q) := by
    dsimp [R]
    by_cases h : c ≤ Real.sqrt q
    · rw [min_eq_left h,min_eq_right ((div_le_one hs).mpr h)]
    · have h' : Real.sqrt q ≤ c := (lt_of_not_ge h).le
      rw [min_eq_right h',div_self hs.ne',min_eq_left ((one_le_div hs).mpr h')]
  have hi : R*(Real.exp (-2)/Real.sqrt (2*Real.pi*q)) ≤
      (gaussianReal 0 v).real (Ioo 0 R) := by
    rw [gaussian_mass_density 0 (show 0 < v from hv)]
    calc
      _ = ∫ _ in Ioo (0 : ℝ) R, Real.exp (-2)/Real.sqrt (2*Real.pi*q) := by
        rw [setIntegral_const,Real.volume_real_Ioo_of_le hR]
        simp
      _ ≤ _ := by
        apply setIntegral_mono_on
          (integrableOn_const (μ := volume) (s := Ioo (0 : ℝ) R)
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          (integrable_gaussianPDFReal 0 v).integrableOn measurableSet_Ioo
        intro z hz
        apply gaussian_density_lower hq hl hu
        have hzs : z ≤ Real.sqrt q := hz.2.le.trans hRs
        nlinarith [Real.sq_sqrt hq.le,hz.1]
  have he : R*(Real.exp (-2)/Real.sqrt (2*Real.pi*q)) =
      intervalLowerConstant*min 1 (c/Real.sqrt q) := by
    rw [← hr,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]
    unfold intervalLowerConstant
    ring
  rw [he] at hi
  exact hi.trans (measureReal_mono (μ := gaussianReal 0 v)
    (fun _ hz => ⟨hz.1,hz.2.trans_le hRc⟩) (by finiteness))

theorem gaussian_positive_interval_tail {v : NNReal} (hv : 0 < v) {c : ℝ} (hc : 0 < c) :
    (gaussianReal 0 v).real (Ioo 0 c)+(gaussianReal 0 v).real (Ici c) = 1/2 := by
  have he : Ioo (0 : ℝ) c ∪ Ici c = Ioi (0 : ℝ) := by
    ext z
    simp only [Set.mem_union,Set.mem_Ioo,Set.mem_Ici,Set.mem_Ioi]
    constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact hc.trans_le hz
    · intro hz
      by_cases hzc : z < c
      · exact Or.inl ⟨hz,hzc⟩
      · exact Or.inr (le_of_not_gt hzc)
  have hd : Disjoint (Ioo (0 : ℝ) c) (Ici c) := by
    rw [Set.disjoint_left]
    exact fun _ hz hc => not_lt_of_ge hc hz.2
  rw [← measureReal_union hd measurableSet_Ici,he,gaussian_positive_half hv]

end NField.Alignment.HarperGaussianCentralLower
