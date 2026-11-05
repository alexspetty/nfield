/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralLowerMoments
import NField.Alignment.CollisionSpectralErrorBound

/-!
# Comparing the actual Jordan energy with its leading spectral term

The error is bounded by the actual conductor moment majorant. Constants are
fixed independently of the conductor and cutoff.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralEnergyError

open scoped BigOperators Classical
open Filter
open CollisionJordanVariance CollisionConductorArithmetic CollisionZetaMoments
open CollisionHarmonicSeed CollisionUniformAmplitude CollisionSpectralErrorBound
open CollisionSpectralArithmetic CollisionSpectralAbel CollisionSpectralNuBounds
open CollisionLogTailKernel CollisionPositiveLogTail CollisionSpectralLowerMoments

def leadingAmplitude (q : ℕ) : ℝ := amplitudeLeading*rho q*Real.log q/(q : ℝ)^2
def residualAmplitude (q : ℕ) : ℝ := amplitude q-leadingAmplitude q
def residualConstant : ℝ := amplitudeLeading*|kappaZero|+coarseErrorFactor
def energyErrorConstant : ℝ := 2*amplitudeLeading*(residualConstant+amplitudeLeading)+
  2*(residualConstant^2+amplitudeLeading^2)
def energyResidual (q : ℕ) : ℝ := conductorEnergy q-amplitudeLeading^2*weightedTerm q
def energyResidualTail (Q : ℝ) : ℝ :=
  ∑' q : ℕ, if Q < (q : ℝ) then energyResidual q else 0

theorem spectralLeading_pos : 0 < amplitudeLeading := by
  unfold amplitudeLeading
  exact div_pos (zetaNat_pos (by norm_num)) zetaThree_pos

theorem residualConstant_pos : 0 < residualConstant := by
  unfold residualConstant
  positivity [spectralLeading_pos,coarseErrorFactor_pos]

theorem energyErrorConstant_pos : 0 < energyErrorConstant := by
  unfold energyErrorConstant
  positivity [spectralLeading_pos,residualConstant_pos]

theorem leadingAmplitude_nonneg {q : ℕ} (hq : 0 < q) : 0 ≤ leadingAmplitude q := by
  unfold leadingAmplitude
  positivity [spectralLeading_pos,rho_nonneg hq,Real.log_natCast_nonneg q]

theorem leadingAmplitude_bound {q : ℕ} (hq : 0 < q) :
    leadingAmplitude q ≤ amplitudeLeading*Real.log q/(q : ℝ)^2 := by
  unfold leadingAmplitude
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rho_le_one hq) spectralLeading_pos.le)
    (Real.log_natCast_nonneg q)
  simpa only [mul_one] using div_le_div_of_nonneg_right h (sq_nonneg (q : ℝ))

theorem residualAmplitude_formula {q : ℕ} (hq : 2 ≤ q) :
    residualAmplitude q = amplitudeLeading*rho q/(q : ℝ)^2*(kappaZero+nu q)+amplitudeError q := by
  unfold residualAmplitude
  rw [amplitude_uniform_formula hq]
  unfold leadingAmplitude
  ring

theorem residualAmplitude_bound {q : ℕ} (hq : 2 ≤ q) :
    |residualAmplitude q| ≤ (residualConstant+amplitudeLeading*nu q)/(q : ℝ)^2 := by
  have hq0 : 0 < q := by omega
  have hc : 0 ≤ amplitudeLeading*rho q/(q : ℝ)^2 := by
    positivity [spectralLeading_pos,rho_nonneg hq0]
  have hcoef : amplitudeLeading*rho q/(q : ℝ)^2 ≤ amplitudeLeading/(q : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left (rho_le_one hq0) spectralLeading_pos.le
    simpa only [mul_one] using div_le_div_of_nonneg_right h (sq_nonneg (q : ℝ))
  rw [residualAmplitude_formula hq]
  calc
    _ ≤ |amplitudeLeading*rho q/(q : ℝ)^2*(kappaZero+nu q)|+|amplitudeError q| := abs_add_le _ _
    _ ≤ (amplitudeLeading/(q : ℝ)^2)*(|kappaZero|+nu q)+coarseErrorFactor/(q : ℝ)^2 := by
      apply add_le_add _ (amplitude_error_inverse_square hq0)
      rw [abs_mul,abs_of_nonneg hc]
      have habs : |kappaZero+nu q| ≤ |kappaZero|+nu q := by
        simpa only [abs_of_nonneg (nu_nonneg q)] using abs_add_le kappaZero (nu q)
      exact (mul_le_mul_of_nonneg_left habs hc).trans
        (mul_le_mul_of_nonneg_right hcoef (add_nonneg (abs_nonneg _) (nu_nonneg q)))
    _ = _ := by unfold residualConstant; ring

theorem jordan_leading_square (q : ℕ) :
    jordanTwo q*(leadingAmplitude q)^2=amplitudeLeading^2*weightedTerm q := by
  unfold leadingAmplitude weightedTerm logPowerKernel spectralWeight
  ring

theorem energyResidual_identity {q : ℕ} (hq : 2 ≤ q) :
    energyResidual q = jordanTwo q*(2*leadingAmplitude q*residualAmplitude q+(residualAmplitude q)^2) := by
  rw [energyResidual,conductorEnergy,if_pos hq,← jordan_leading_square]
  unfold residualAmplitude
  ring

theorem scalar_square_error_bound {J b r : ℝ} (hJ : 0 ≤ J) (hb : 0 ≤ b) :
    |J*(2*b*r+r^2)| ≤ J*(2*b*|r|+|r|^2) := by
  rw [abs_mul,abs_of_nonneg hJ]
  apply mul_le_mul_of_nonneg_left _ hJ
  calc
    _ ≤ |2*b*r|+|r^2| := abs_add_le _ _
    _ = _ := by simp only [abs_mul,abs_of_nonneg hb,abs_pow]; norm_num

theorem energyResidual_raw_bound {q : ℕ} (hq : 2 ≤ q) :
    |energyResidual q| ≤
      (2*amplitudeLeading*Real.log q*(residualConstant+amplitudeLeading*nu q)+
        (residualConstant+amplitudeLeading*nu q)^2)/(q : ℝ)^2 := by
  have hq0 : 0 < q := by omega
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq0.ne'
  have hR : 0 ≤ residualConstant+amplitudeLeading*nu q := by
    positivity [residualConstant_pos,spectralLeading_pos,nu_nonneg q]
  have hL := Real.log_natCast_nonneg q
  rw [energyResidual_identity hq]
  calc
    _ ≤ jordanTwo q*(2*leadingAmplitude q*|residualAmplitude q|+|residualAmplitude q|^2) :=
      scalar_square_error_bound (jordanTwo_nonneg q) (leadingAmplitude_nonneg hq0)
    _ ≤ (q : ℝ)^2*(2*(amplitudeLeading*Real.log q/(q : ℝ)^2)*
          ((residualConstant+amplitudeLeading*nu q)/(q : ℝ)^2)+
          ((residualConstant+amplitudeLeading*nu q)/(q : ℝ)^2)^2) := by
      apply mul_le_mul (jordanTwo_le_square hq0) _
        (by positivity [leadingAmplitude_nonneg hq0]) (sq_nonneg (q : ℝ))
      apply add_le_add
      · apply mul_le_mul
          (mul_le_mul_of_nonneg_left (leadingAmplitude_bound hq0) (by norm_num : (0 : ℝ) ≤ 2))
          (residualAmplitude_bound hq) (abs_nonneg _)
        positivity [spectralLeading_pos]
      · exact pow_le_pow_left₀ (abs_nonneg _) (residualAmplitude_bound hq) 2
    _ = _ := by field_simp

theorem scalar_moment_majorant {A C L V : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hL : 0 ≤ L) :
    2*A*L*(C+A*V)+(C+A*V)^2 ≤
      (2*A*(C+A)+2*(C^2+A^2))*(1+L)*(1+V^2) := by
  have hVb : V ≤ 1+V^2 := by nlinarith [sq_nonneg (V-1/2)]
  have hCb : C ≤ C*(1+V^2) := le_mul_of_one_le_right hC (by nlinarith [sq_nonneg V])
  have hR : C+A*V ≤ (C+A)*(1+V^2) := by
    have h := add_le_add hCb (mul_le_mul_of_nonneg_left hVb hA)
    convert! h using 1
    ring
  have hR2 : (C+A*V)^2 ≤ 2*(C^2+A^2)*(1+V^2) := by
    nlinarith [sq_nonneg (C-A*V),mul_nonneg (sq_nonneg C) (sq_nonneg V),sq_nonneg A]
  have hF : 0 ≤ 1+V^2 := by positivity
  have hK1 : 0 ≤ 2*A*(C+A) := by positivity
  have hK2 : 0 ≤ 2*(C^2+A^2) := by positivity
  calc
    _ ≤ 2*A*L*((C+A)*(1+V^2))+2*(C^2+A^2)*(1+V^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hR (by positivity)) hR2
    _ = (2*A*(C+A))*L*(1+V^2)+2*(C^2+A^2)*(1+V^2) := by ring
    _ ≤ (2*A*(C+A))*(1+L)*(1+V^2)+2*(C^2+A^2)*(1+L)*(1+V^2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : L ≤ 1+L) hK1) hF
      · exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK2 (by linarith)) hF
    _ = _ := by ring

theorem energyResidual_bound_ge_two {q : ℕ} (hq : 2 ≤ q) :
    |energyResidual q| ≤ energyErrorConstant*positiveLogTerm momentMajorant q := by
  have hq0 : q≠0 := by omega
  calc
    _ ≤ (2*amplitudeLeading*Real.log q*(residualConstant+amplitudeLeading*nu q)+
        (residualConstant+amplitudeLeading*nu q)^2)/(q : ℝ)^2 := energyResidual_raw_bound hq
    _ ≤ (2*amplitudeLeading*(residualConstant+amplitudeLeading)+
        2*(residualConstant^2+amplitudeLeading^2))*(1+Real.log q)*(1+(nu q)^2)/(q : ℝ)^2 :=
      div_le_div_of_nonneg_right (scalar_moment_majorant spectralLeading_pos.le
        residualConstant_pos.le (Real.log_natCast_nonneg q)) (sq_nonneg (q : ℝ))
    _ = _ := by
      unfold energyErrorConstant positiveLogTerm positiveLogKernel momentMajorant
      rw [if_neg hq0]
      ring

theorem energyResidual_small {q : ℕ} (hq : q < 2) : energyResidual q=0 := by
  interval_cases q <;> simp [energyResidual,conductorEnergy,weightedTerm,logPowerKernel]

theorem energyResidual_bound (q : ℕ) :
    |energyResidual q| ≤ energyErrorConstant*positiveLogTerm momentMajorant q := by
  by_cases hq : 2 ≤ q
  · exact energyResidual_bound_ge_two hq
  · rw [energyResidual_small (by omega),abs_zero]
    exact mul_nonneg energyErrorConstant_pos.le
      (mul_nonneg (positiveLogKernel_nat_nonneg q) (momentMajorant_nonneg q))

theorem energyResidual_summable : Summable energyResidual :=
  conductorEnergy_summable.sub (weightedTerm_summable.mul_left (amplitudeLeading^2))

theorem energyResidual_tail_summable (Q : ℝ) :
    Summable (fun q : ℕ => if Q < (q : ℝ) then energyResidual q else 0) := by
  have h := energyResidual_summable.indicator {q : ℕ | Q < (q : ℝ)}
  apply h.congr
  intro q
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem energyResidual_tail_bound {Q : ℝ} (hQ : 1 ≤ Q) :
    |energyResidualTail Q| ≤ energyErrorConstant*positiveLogTail momentMajorant Q := by
  have hs := energyResidual_tail_summable Q
  have hbound : ∀ q : ℕ, ‖if Q < (q : ℝ) then energyResidual q else 0‖ ≤
      energyErrorConstant*(if Q < (q : ℝ) then positiveLogTerm momentMajorant q else 0) := by
    intro q
    split_ifs
    · simpa only [Real.norm_eq_abs] using energyResidual_bound q
    · simp
  have h := hs.norm.tsum_le_tsum hbound
    ((momentMajorant_tail_summable hQ).mul_left energyErrorConstant)
  rw [tsum_mul_left] at h
  exact (show |energyResidualTail Q| ≤ ∑' q : ℕ,
      ‖if Q < (q : ℝ) then energyResidual q else 0‖ by
    exact norm_tsum_le_tsum_norm hs.norm).trans h

theorem energyResidual_tail_isBigO_moment :
    Asymptotics.IsBigO atTop energyResidualTail (positiveLogTail momentMajorant) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨energyErrorConstant,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Q hQ
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (positiveLog_tail_nonneg momentMajorant_nonneg Q)]
  exact energyResidual_tail_bound hQ

theorem energyResidual_tail_isBigO :
    Asymptotics.IsBigO atTop energyResidualTail (fun Q : ℝ => Real.log Q/Q) :=
  energyResidual_tail_isBigO_moment.trans momentMajorant_tail_isBigO

theorem energyResidual_tail_isLittleO :
    Asymptotics.IsLittleO atTop energyResidualTail (fun Q : ℝ => (Real.log Q)^2/Q) :=
  energyResidual_tail_isBigO_moment.trans_isLittleO momentMajorant_tail_isLittleO

end NField.Alignment.CollisionSpectralEnergyError
