/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianTail

/-!
# Gaussian overshoots and the one-step killed deficit

For a nonnegative threshold and variance in (0,1], expected positive
overshoot is at most twice the crossing probability. The one-step
surviving deficit therefore increases by at most that same amount.
Adding two on survival gives a nonnegative integrable killed potential
whose expectation is at most the initial deficit plus two. Iterating
this bound along the actual finite path and deriving survival estimates
remain separate obligations.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianOvershoot
open MeasureTheory ProbabilityTheory Set HarperGaussianTail

theorem gaussian_identity_integrable (m : ℝ) (v : NNReal) :
    Integrable (fun z : ℝ => z) (gaussianReal m v) :=
  memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by norm_num))

theorem gaussian_overshoot_integrable (m a : ℝ) (v : NNReal) :
    Integrable (fun z => max (z-a) 0) (gaussianReal m v) :=
  ((gaussian_identity_integrable m v).sub (integrable_const a)).sup (integrable_const 0)

theorem gaussian_deficit_integrable (m d : ℝ) (v : NNReal) :
    Integrable (fun z => max (d-z) 0) (gaussianReal m v) :=
  ((integrable_const d).sub (gaussian_identity_integrable m v)).sup (integrable_const 0)

theorem gaussian_overshoot_layercake (a : ℝ) (v : NNReal) :
    (∫ z, max (z-a) 0 ∂gaussianReal 0 v) =
      ∫ r in Ioi (0 : ℝ), (gaussianReal 0 v).real (Ioi (a+r)) := by
  rw [(gaussian_overshoot_integrable 0 a v).integral_eq_integral_meas_lt
    (ae_of_all _ (fun z => le_max_right (z-a) 0))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have he : {z : ℝ | r < max (z-a) 0} = Ioi (a+r) := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ioi]
    constructor
    · intro h
      rcases lt_max_iff.mp h with h | h
      · linarith
      · have : 0 < r := hr
        linarith
    · intro h
      exact lt_of_lt_of_le (by linarith : r < z-a) (le_max_left _ _)
  change (gaussianReal 0 v).real {z : ℝ | r < max (z-a) 0} = _
  rw [he]

theorem gaussian_overshoot_le_twice_tail {v : NNReal} (hv : 0 < v)
    (hv1 : (v : ℝ) ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, max (z-a) 0 ∂gaussianReal 0 v) ≤ 2*(gaussianReal 0 v).real (Ioi a) := by
  rw [gaussian_overshoot_layercake]
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), Real.exp (-r^2/(2*v))*(gaussianReal 0 v).real (Ioi a) := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun r => measureReal_nonneg))
        ((gaussian_tail_envelope_integrable hv).integrableOn.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact gaussian_tail_shift hv ha hr.le
    _ = (∫ r in Ioi (0 : ℝ), Real.exp (-r^2/(2*v)))*(gaussianReal 0 v).real (Ioi a) :=
      integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (gaussian_tail_envelope_integral_le_two hv hv1)
      measureReal_nonneg

theorem killed_deficit_eq_positivePart (d z : ℝ) :
    (Iic d).indicator (fun y => d-y) z = max (d-z) 0 := by
  by_cases hz : z ≤ d
  · rw [Set.indicator_of_mem (show z ∈ Iic d from hz),max_eq_left (by linarith)]
  · rw [Set.indicator_of_notMem (show z ∉ Iic d from hz),max_eq_right (by linarith)]

theorem gaussian_deficit_identity (d : ℝ) (v : NNReal) :
    (∫ z, max (d-z) 0 ∂gaussianReal 0 v) = d+∫ z, max (z-d) 0 ∂gaussianReal 0 v := by
  have he (z : ℝ) : max (d-z) 0 = d-z+max (z-d) 0 := by
    by_cases hz : z ≤ d
    · rw [max_eq_left (by linarith : 0 ≤ d-z),max_eq_right (by linarith : z-d ≤ 0)]
      ring
    · rw [max_eq_right (by linarith : d-z ≤ 0),max_eq_left (by linarith : 0 ≤ z-d)]
      ring
  simp_rw [he]
  have hi : Integrable (fun z : ℝ => d-z) (gaussianReal 0 v) :=
    (integrable_const d).sub (gaussian_identity_integrable 0 v)
  rw [integral_add hi
    (gaussian_overshoot_integrable 0 d v),
    integral_sub (integrable_const d) (gaussian_identity_integrable 0 v),
    integral_id_gaussianReal]
  simp

theorem gaussian_killed_deficit_one_step {v : NNReal} (hv : 0 < v)
    (hv1 : (v : ℝ) ≤ 1) {d : ℝ} (hd : 0 ≤ d) :
    (∫ z, (Iic d).indicator (fun y => d-y) z ∂gaussianReal 0 v) ≤
      d+2*(gaussianReal 0 v).real (Ioi d) := by
  simp_rw [killed_deficit_eq_positivePart]
  rw [gaussian_deficit_identity]
  linarith [gaussian_overshoot_le_twice_tail hv hv1 hd]

/-- The deficit plus two, set to zero once the increment crosses the barrier. -/
def killedPotential (d z : ℝ) : ℝ :=
  (Iic d).indicator (fun y => d-y+2) z

theorem killedPotential_nonneg (d z : ℝ) : 0 ≤ killedPotential d z := by
  unfold killedPotential
  by_cases hz : z ∈ Iic d
  · rw [Set.indicator_of_mem hz]
    have : z ≤ d := hz
    linarith
  · rw [Set.indicator_of_notMem hz]

theorem gaussian_killedPotential_integrable (m d : ℝ) (v : NNReal) :
    Integrable (killedPotential d) (gaussianReal m v) := by
  exact (((integrable_const d).sub (gaussian_identity_integrable m v)).add
    (integrable_const 2)).indicator measurableSet_Iic

theorem gaussian_killedPotential_integral (d : ℝ) (v : NNReal) :
    (∫ z, killedPotential d z ∂gaussianReal 0 v) =
      (∫ z, max (d-z) 0 ∂gaussianReal 0 v) +
        2*(gaussianReal 0 v).real (Iic d) := by
  have he (z : ℝ) : killedPotential d z =
      max (d-z) 0 + (Iic d).indicator (fun _ : ℝ => (2 : ℝ)) z := by
    rw [← killed_deficit_eq_positivePart]
    unfold killedPotential
    by_cases hz : z ∈ Iic d
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz,add_zero]
  simp_rw [he]
  rw [integral_add (gaussian_deficit_integrable 0 d v)
    ((integrable_const (2 : ℝ)).indicator measurableSet_Iic),
    integral_indicator_const (2 : ℝ) measurableSet_Iic]
  simp only [smul_eq_mul,mul_comm]

theorem gaussian_killedPotential_one_step {v : NNReal} (hv : 0 < v)
    (hv1 : (v : ℝ) ≤ 1) {d : ℝ} (hd : 0 ≤ d) :
    (∫ z, killedPotential d z ∂gaussianReal 0 v) ≤ d+2 := by
  rw [gaussian_killedPotential_integral,gaussian_deficit_identity]
  have hm : (gaussianReal 0 v).real (Iic d) +
      (gaussianReal 0 v).real (Ioi d) = 1 := by
    simpa only [compl_Iic,probReal_univ] using
      (measureReal_add_measureReal_compl (μ := gaussianReal 0 v) measurableSet_Iic)
  linarith [gaussian_overshoot_le_twice_tail hv hv1 hd]

end NField.Alignment.HarperGaussianOvershoot
