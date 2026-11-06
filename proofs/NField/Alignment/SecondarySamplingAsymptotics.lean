/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerTransformBounds
import NField.Alignment.SquareLockAsymptoticScales

/-! # The actual all-prime sampling defect is little-o of logarithm squared -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondarySamplingAsymptotics
open scoped Topology
open Filter Asymptotics PrimeCarrierDamping PrimeSecondaryCoefficient
  SquareLockAsymptoticScales

theorem log_square_eventually_ne_zero :
    ∀ᶠ p : ℕ in atTop,Real.log (p : ℝ)^2≠0 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
  exact pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (show 1<p by omega))).ne'

theorem one_isLittleO_log_square :
    (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun p => Real.log (p : ℝ)^2) := by
  apply (isLittleO_iff_tendsto' (log_square_eventually_ne_zero.mono
    (fun p hp hz => (hp hz).elim))).mpr
  have hi := tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  simpa only [Function.comp_def,one_div,inv_pow,zero_pow (by decide : (2 : ℕ)≠0)] using hi.pow 2

theorem logarithmic_sampling_scale_isLittleO :
    logarithmicCarrierSamplingScale =o[atTop] (fun p => Real.log (p : ℝ)^2) := by
  have hden : Tendsto (fun p : ℕ => Real.log (Real.log (3*(p : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by norm_num : (0 : ℝ)<3)))
  apply (isLittleO_iff_tendsto' (log_square_eventually_ne_zero.mono
    (fun p hp hz => (hp hz).elim))).mpr
  apply squeeze_zero' (g := fun p : ℕ => 4/Real.log (Real.log (3*(p : ℝ))))
  · exact Eventually.of_forall (fun p => div_nonneg
      (logarithmicCarrierSamplingScale_nonneg p) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop (2 : ℕ),hden.eventually_ge_atTop 1] with p hp hd
    have hl : 0<Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1<p by omega))
    have hdouble := log_double_le hp
    have hs : Real.log (2*(p : ℝ))^2 ≤ 4*Real.log (p : ℝ)^2 := by
      nlinarith
    have hquot : Real.log (2*(p : ℝ))^2/Real.log (p : ℝ)^2 ≤ 4 :=
      (div_le_iff₀ (sq_pos_of_pos hl)).mpr hs
    change logarithmicCarrierSamplingScale p/Real.log (p : ℝ)^2 ≤ _
    unfold logarithmicCarrierSamplingScale
    rw [if_pos hp]
    calc
      _ = (Real.log (2*(p : ℝ))^2/Real.log (p : ℝ)^2)/
          Real.log (Real.log (3*(p : ℝ))) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hquot (by linarith)
  · simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul 4

theorem sampling_defect_isBigO_printed :
    primeSamplingDefect =O[primeAtTop] (fun p => 1+logarithmicCarrierSamplingScale p) := by
  obtain ⟨C,hC,hbound⟩ :=
    (all_prime_carrier_damping_from_analytic_inputs IntegerTransformBounds.ambient_inverse_bound).2
  apply IsBigO.of_bound C
  have hp : ∀ᶠ p in primeAtTop,p.Prime :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hp => hp)
  filter_upwards [hp,(eventually_ge_atTop (3 : ℕ)).filter_mono inf_le_left] with p hp hp3
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by positivity [logarithmicCarrierSamplingScale_nonneg p])]
  exact hbound p hp (by omega)

/-- Title: `The all-prime sampling defect is negligible at logarithm squared`. -/
theorem sampling_defect_isLittleO_log_square :
    primeSamplingDefect =o[primeAtTop] (fun p => Real.log (p : ℝ)^2) :=
  sampling_defect_isBigO_printed.trans_isLittleO
    ((one_isLittleO_log_square.add logarithmic_sampling_scale_isLittleO).mono inf_le_left)

end NField.Alignment.SecondarySamplingAsymptotics
