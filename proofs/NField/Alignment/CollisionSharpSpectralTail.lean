/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralEnergyError
import NField.Alignment.CollisionConductorFourierSpace

/-!
# Sharp Haar spectral tail

The actual orthogonal projection onto the full additive-conductor space
has the manuscript's sharp asymptotic, including its exact constant.
Real cutoffs use the natural floor, which selects exactly the same conductors.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSharpSpectralTail

open scoped BigOperators Classical
open Filter
open CollisionPotentialConvergence CollisionJordanVariance CollisionZetaMoments
open CollisionConductorArithmetic CollisionConductorFourierSpace
open CollisionSpectralEuler CollisionSpectralAbel CollisionSpectralTailMean
open CollisionSpectralEnergyError

def spectralEnergyTail (Q : ℝ) : ℝ :=
  ∑' q : ℕ, if Q < (q : ℝ) then conductorEnergy q else 0

def spectralProjectionError (Q : ℝ) : ℝ :=
  ‖collisionPotential-(additiveConductorSpace ⌊Q⌋₊).starProjection collisionPotential‖^2

theorem spectralEnergy_tail_summable (Q : ℝ) :
    Summable (fun q : ℕ => if Q < (q : ℝ) then conductorEnergy q else 0) := by
  apply (conductorEnergy_summable.indicator {q : ℕ | Q < (q : ℝ)}).congr
  intro q
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem spectralWeighted_tail_summable (Q : ℝ) :
    Summable (fun q : ℕ => if Q < (q : ℝ) then weightedTerm q else 0) := by
  apply (weightedTerm_summable.indicator {q : ℕ | Q < (q : ℝ)}).congr
  intro q
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem spectralEnergy_tail_decomposition (Q : ℝ) :
    spectralEnergyTail Q=amplitudeLeading^2*weightedTail Q+energyResidualTail Q := by
  calc
    _ = ∑' q : ℕ, (amplitudeLeading^2*(if Q < (q : ℝ) then weightedTerm q else 0)+
        (if Q < (q : ℝ) then energyResidual q else 0)) := by
      apply tsum_congr
      intro q
      by_cases hq : Q < (q : ℝ)
      · simp only [if_pos hq,energyResidual]
        ring
      · simp only [if_neg hq,mul_zero,zero_add]
    _ = _ := by
      rw [Summable.tsum_add ((spectralWeighted_tail_summable Q).mul_left (amplitudeLeading^2))
        (energyResidual_tail_summable Q),tsum_mul_left]
      rfl

theorem spectralEnergy_tail_leading_mean :
    Tendsto (fun Q : ℝ => spectralEnergyTail Q/((Real.log Q)^2/Q))
      atTop (nhds (amplitudeLeading^2*spectralConstant)) := by
  have h := (weighted_tail_leading_mean.const_mul (amplitudeLeading^2)).add
    energyResidual_tail_isLittleO.tendsto_div_nhds_zero
  simp only [add_zero] at h
  convert! h using 1
  funext Q
  rw [spectralEnergy_tail_decomposition]
  ring

theorem spectralEnergy_tail_asymptotic :
    Asymptotics.IsEquivalent atTop spectralEnergyTail
      (fun Q : ℝ => (amplitudeLeading^2*spectralConstant)*(Real.log Q)^2/Q) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hC : amplitudeLeading^2*spectralConstant≠0 := by
    positivity [spectralLeading_pos,spectralConstant_pos]
  have h := spectralEnergy_tail_leading_mean.div_const (amplitudeLeading^2*spectralConstant)
  rw [div_self hC] at h
  convert! h using 1
  funext Q
  simp only [Pi.div_apply,div_div]
  congr 1
  ring

theorem spectralProjectionError_exact {Q : ℝ} (hQ : 1 ≤ Q) :
    spectralProjectionError Q=(1/27 : ℝ)*spectralEnergyTail Q := by
  have hQ0 : 0 ≤ Q := by linarith
  have hfloor : 1 ≤ ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  rw [spectralProjectionError,additive_conductor_tail hfloor]
  congr 1
  apply tsum_congr
  intro q
  simp only [Nat.floor_lt hQ0]
  split_ifs with hq
  · have hq2 : 2 ≤ q := by
      have h : (1 : ℝ) < q := hQ.trans_lt hq
      have hn : 1 < q := by exact_mod_cast h
      omega
    simp only [conductorEnergy,if_pos hq2]
  · rfl

theorem spectralProjectionError_leading_mean :
    Tendsto (fun Q : ℝ => spectralProjectionError Q/((Real.log Q)^2/Q))
      atTop (nhds (amplitudeLeading^2*spectralConstant/27)) := by
  have h := spectralEnergy_tail_leading_mean.const_mul (1/27 : ℝ)
  have hc : (1/27 : ℝ)*(amplitudeLeading^2*spectralConstant)=
      amplitudeLeading^2*spectralConstant/27 := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Q hQ
  rw [spectralProjectionError_exact hQ]
  ring

theorem spectralProjectionError_asymptotic :
    Asymptotics.IsEquivalent atTop spectralProjectionError
      (fun Q : ℝ => (amplitudeLeading^2*spectralConstant/27)*(Real.log Q)^2/Q) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hC : amplitudeLeading^2*spectralConstant/27≠0 := by
    positivity [spectralLeading_pos,spectralConstant_pos]
  have h := spectralProjectionError_leading_mean.div_const (amplitudeLeading^2*spectralConstant/27)
  rw [div_self hC] at h
  convert! h using 1
  funext Q
  simp only [Pi.div_apply,div_div]
  congr 1
  ring

theorem sharp_haar_spectral_tail :
    spectralConstant=(∏' p : Nat.Primes,
      (1+((1-((p.val : ℝ)^2)⁻¹)*(rho p.val)^2-1)/(p.val : ℝ))) ∧
    0 < spectralConstant ∧
    Asymptotics.IsEquivalent atTop
      (fun Q : ℝ =>
        ‖collisionPotential-(additiveConductorSpace ⌊Q⌋₊).starProjection collisionPotential‖^2)
      (fun Q : ℝ => (amplitudeLeading^2*spectralConstant/27)*(Real.log Q)^2/Q) :=
  ⟨spectralConstant_literal_product,spectralConstant_pos,spectralProjectionError_asymptotic⟩

end NField.Alignment.CollisionSharpSpectralTail
