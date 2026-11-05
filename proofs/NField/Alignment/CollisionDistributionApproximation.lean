/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDistributionComparison
import NField.Alignment.CollisionPotentialCutoff

/-!
# Uniform distribution-function approximation by the actual cutoffs

The continuous cutoff observable and the infinite L2 potential share the
same Haar space. Their proved L2 error and the one-quarter concentration
bound give the literal one-ninth rate, uniformly in the threshold.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDistributionApproximation

open scoped Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialCutoff
open CollisionPotentialConcentration CollisionDistributionComparison

def distributionScale (M : ℕ) : ℝ := (Real.log (2*(M : ℝ)))^2/(M : ℝ)

theorem distributionScale_pos {M : ℕ} (hM : 1≤M) : 0<distributionScale M := by
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  exact div_pos (sq_pos_of_pos (Real.log_pos (by linarith))) (by linarith)

theorem finitePotential_coe_map (M : ℕ) :
    (fun x => finitePotential collisionWeight M x) =ᵐ[phaseHaar]
      (fun x => potentialMap collisionWeight M x) := by
  rw [finitePotential_toLp]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (potentialMap collisionWeight M)

theorem cutoff_error_vector_coe (M : ℕ) :
    (fun x => (finitePotential collisionWeight M-collisionPotential) x) =ᵐ[phaseHaar]
      (fun x => potentialMap collisionWeight M x-collisionPotential x) := by
  filter_upwards [Lp.coeFn_sub (finitePotential collisionWeight M) collisionPotential,
    finitePotential_coe_map M] with x hx hf
  simp only [Pi.sub_apply] at hx
  rw [hx,hf]

theorem cutoff_error_sq_integrable (M : ℕ) :
    Integrable (fun x => (potentialMap collisionWeight M x-collisionPotential x)^2) phaseHaar := by
  have hm := (memLp_congr_ae (cutoff_error_vector_coe M)).mp
    (Lp.memLp (finitePotential collisionWeight M-collisionPotential))
  exact hm.integrable_sq

theorem cutoff_error_second_moment (M : ℕ) :
    (∫ x, (potentialMap collisionWeight M x-collisionPotential x)^2 ∂phaseHaar)=
      ‖collisionPotential-finitePotential collisionWeight M‖^2 := by
  rw [norm_sub_rev,← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoff_error_vector_coe M] with x hx
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]

theorem cutoff_norm_log_uniform {M : ℕ} (hM : 1≤M) :
    ‖collisionPotential-finitePotential collisionWeight M‖≤
      (cutoffConstant*(1+1/Real.log 2))*Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ) := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2≤Real.log (2*(M : ℝ)) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤2*M by omega))
  have hr : 1≤Real.log (2*(M : ℝ))/Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using hl)
  have hlog : 1+Real.log (2*(M : ℝ))≤(1+1/Real.log 2)*Real.log (2*(M : ℝ)) := by
    calc
      _ ≤ Real.log (2*(M : ℝ))/Real.log 2+Real.log (2*(M : ℝ)) := add_le_add hr le_rfl
      _ = _ := by ring
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog cutoffConstant_nonneg) (Real.sqrt_nonneg (M : ℝ))
  exact (collisionPotential_cutoff_bound hM).trans (by simpa only [mul_assoc] using hb)

theorem cutoff_variance_uniform : ∃ B : ℝ, 0<B ∧ ∀ M : ℕ, 1≤M →
    (∫ x, (potentialMap collisionWeight M x-collisionPotential x)^2 ∂phaseHaar)≤
      B*distributionScale M := by
  let K : ℝ := cutoffConstant*(1+1/Real.log 2)
  have hK : 0≤K := by
    have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    exact mul_nonneg cutoffConstant_nonneg (by positivity)
  refine ⟨K^2+1,by positivity,?_⟩
  intro M hM
  have hm : (0 : ℝ)<M := by exact_mod_cast hM
  have hl : 0≤Real.log (2*(M : ℝ)) := Real.log_nonneg (by
    have hh : (1 : ℝ)≤M := by exact_mod_cast hM
    linarith)
  have hb := cutoff_norm_log_uniform hM
  change ‖collisionPotential-finitePotential collisionWeight M‖≤
    K*Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ) at hb
  have he : (K*Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ))^2=K^2*distributionScale M := by
    rw [div_pow,mul_pow,Real.sq_sqrt hm.le]
    unfold distributionScale
    ring
  rw [cutoff_error_second_moment]
  have hs : ‖collisionPotential-finitePotential collisionWeight M‖^2≤
      (K*Real.log (2*(M : ℝ))/Real.sqrt (M : ℝ))^2 := by
    nlinarith [norm_nonneg (collisionPotential-finitePotential collisionWeight M)]
  rw [he] at hs
  nlinarith [distributionScale_pos hM]

theorem cutoff_distribution_uniform : ∃ K : ℝ, 0<K ∧ ∀ M : ℕ, 1≤M → ∀ u : ℝ,
    |phaseHaar.real {x | potentialMap collisionWeight M x≤u}-
      phaseHaar.real {x | collisionPotential x≤u}|≤
      K*((Real.log (2*(M : ℝ)))^2/(M : ℝ))^(1/(9 : ℝ)) := by
  obtain ⟨C,hC,hQ⟩ := potential_interval_bound
  obtain ⟨B,hB,hE⟩ := cutoff_variance_uniform
  refine ⟨C+B+1,by linarith,?_⟩
  intro M hM u
  exact distribution_ninth_rate phaseHaar (potentialMap collisionWeight M) collisionPotential
    hC.le hB.le (distributionScale_pos hM) (cutoff_error_sq_integrable M) (hE M hM) hQ u

theorem distribution_function_approximation : ∃ K : ℝ, 0<K ∧ ∀ M : ℕ, 1≤M →
    (⨆ u : ℝ, |phaseHaar.real {x | potentialMap collisionWeight M x≤u}-
      phaseHaar.real {x | collisionPotential x≤u}|)≤
      K*((Real.log (2*(M : ℝ)))^2/(M : ℝ))^(1/(9 : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := cutoff_distribution_uniform
  exact ⟨K,hK,fun M hM => ciSup_le (hbound M hM)⟩

end NField.Alignment.CollisionDistributionApproximation
