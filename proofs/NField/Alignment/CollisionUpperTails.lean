/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTailProbability
import NField.Alignment.CollisionTailCutoffScales

/-!
# Uniform stretched-exponential upper tails

The exponential cutoff, exact stationary height and common L2 remainder
give the sharp range 0<c<pi for the potential and every finite cutoff.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionUpperTails

open scoped Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionDistributionApproximation
open CollisionTailProbability CollisionTailCutoffScales

theorem tail_scale_exponential {d H : ℝ} (hH : 1 ≤ H)
    (h4 : 4 ≤ d*Real.sqrt H) :
    distributionScale (tailCutoff d H) ≤
      2*(Real.log 2+d)^2*H*Real.exp (-d*Real.sqrt H) := by
  have hb := exp_floor_bounds h4
  have hL : (0 : ℝ) < tailCutoff d H := by
    exact_mod_cast (show 0 < tailCutoff d H from Nat.lt_of_lt_of_le (by norm_num) hb.1)
  have hH0 : 0 ≤ H := by linarith
  have hs : 1 ≤ Real.sqrt H := Real.le_sqrt_of_sq_le (by simpa using hH)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (2*(tailCutoff d H : ℝ)) ≤ (Real.log 2+d)*Real.sqrt H := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL.ne']
    have hl := log_exp_floor_le h4
    change Real.log (tailCutoff d H) ≤ d*Real.sqrt H at hl
    nlinarith [mul_nonneg h2.le (sub_nonneg.mpr hs)]
  have hlog0 : 0 ≤ Real.log (2*(tailCutoff d H : ℝ)) := Real.log_nonneg (by
    have hh : (3 : ℝ) ≤ tailCutoff d H := by exact_mod_cast hb.1
    linarith)
  have hlogSq : (Real.log (2*(tailCutoff d H : ℝ)))^2 ≤ (Real.log 2+d)^2*H := by
    have hh : (Real.log (2*(tailCutoff d H : ℝ)))^2 ≤
        ((Real.log 2+d)*Real.sqrt H)^2 := pow_le_pow_left₀ hlog0 hlog 2
    rwa [mul_pow,Real.sq_sqrt hH0] at hh
  have hinv : 1/(tailCutoff d H : ℝ) ≤ 2*Real.exp (-d*Real.sqrt H) := by
    have hfrac : 1/(tailCutoff d H : ℝ) ≤ 2/Real.exp (d*Real.sqrt H) := by
      apply (div_le_div_iff₀ hL (Real.exp_pos _)).mpr
      have hh := hb.2.1
      change Real.exp (d*Real.sqrt H)/2 ≤ (tailCutoff d H : ℝ) at hh
      nlinarith
    simpa only [neg_mul,Real.exp_neg,div_eq_mul_inv] using hfrac
  calc
    _ = (Real.log (2*(tailCutoff d H : ℝ)))^2*(1/(tailCutoff d H : ℝ)) := by
      unfold distributionScale
      ring
    _ ≤ ((Real.log 2+d)^2*H)*(2*Real.exp (-d*Real.sqrt H)) :=
      mul_le_mul hlogSq hinv (by positivity) (mul_nonneg (sq_nonneg _) hH0)
    _ = _ := by ring

theorem decay_ratio_bound {B S T δ H A z : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hH : 1 ≤ H)
    (hmargin : δ*H ≤ H-A) (hscale : S ≤ T*H*Real.exp (-z)) :
    B*S/(H-A)^2 ≤ (B*T/δ^2)*Real.exp (-z) := by
  have hH0 : 0 < H := by linarith
  have hdH : 0 < δ*H := mul_pos hδ hH0
  have hden : (δ*H)^2 ≤ (H-A)^2 := by nlinarith
  calc
    _ ≤ B*S/(δ*H)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg hB hS) (sq_pos_of_pos hdH) hden
    _ ≤ B*(T*H*Real.exp (-z))/(δ*H)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hB) (sq_nonneg _)
    _ = ((B*T/δ^2)*Real.exp (-z))/H := by field_simp
    _ ≤ (B*T/δ^2)*Real.exp (-z) := by
      apply (div_le_iff₀ hH0).mpr
      have hn : 0 ≤ (B*T/δ^2)*Real.exp (-z) := by positivity
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hH)]

theorem upper_tails_large {d : ℝ} (hd : 0 < d) (hdπ : d < Real.pi) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ H : ℝ, R ≤ H →
      (phaseHaar.real {x | H < |collisionPotential x|} ≤ C*Real.exp (-d*Real.sqrt H)) ∧
      (∀ M : ℕ, phaseHaar.real {x | H < |potentialMap collisionWeight M x|} ≤
        C*Real.exp (-d*Real.sqrt H)) := by
  obtain ⟨B,hB,hprob⟩ := uniform_tail_variance_bound
  obtain ⟨δ,R,hδ,hδ1,hR,hheight⟩ := tail_cutoff_height hd hdπ
  let T : ℝ := 2*(Real.log 2+d)^2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨B*T/δ^2,R,by positivity,hR,?_⟩
  intro H hH
  obtain ⟨h4,hL3,hage⟩ := hheight H hH
  have hH1 : 1 ≤ H := hR.trans hH
  have hH0 : 0 < H := by linarith
  have hmargin : δ*H ≤ H-stationaryAge collisionWeight (tailCutoff d H) := by linarith
  have hstrict : stationaryAge collisionWeight (tailCutoff d H) < H := by
    nlinarith [mul_pos hδ hH0]
  have hL1 : 1 ≤ tailCutoff d H := by omega
  obtain ⟨hY,hM⟩ := hprob (tailCutoff d H) hL1 H hstrict
  have hs := tail_scale_exponential hH1 h4
  have hdec := decay_ratio_bound hB.le (distributionScale_pos hL1).le hT.le hδ hH1 hmargin
    (by simpa only [T,mul_assoc,neg_mul] using hs)
  exact ⟨hY.trans (by simpa only [neg_mul] using hdec),
    fun M => (hM M).trans (by simpa only [neg_mul] using hdec)⟩

theorem upper_tails {c : ℝ} (hc : 0 < c) (hcπ : c < Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H →
      (phaseHaar.real {x | H < |collisionPotential x|} ≤ K*Real.exp (-c*Real.sqrt H)) ∧
      (∀ M : ℕ, phaseHaar.real {x | H < |potentialMap collisionWeight M x|} ≤
        K*Real.exp (-c*Real.sqrt H)) := by
  let d : ℝ := (c+Real.pi)/2
  have hd : 0 < d := by dsimp [d]; linarith [Real.pi_pos]
  have hdπ : d < Real.pi := by dsimp [d]; linarith
  have hcd : c ≤ d := by dsimp [d]; linarith
  obtain ⟨C,R,hC,hR,hbound⟩ := upper_tails_large hd hdπ
  let K : ℝ := C+Real.exp (c*Real.sqrt R)
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : C ≤ K := by dsimp [K]; linarith [Real.exp_pos (c*Real.sqrt R)]
  have hEK : Real.exp (c*Real.sqrt R) ≤ K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro H hH
  by_cases hRH : R ≤ H
  · obtain ⟨hY,hM⟩ := hbound H hRH
    have he : Real.exp (-d*Real.sqrt H) ≤ Real.exp (-c*Real.sqrt H) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hcd) (Real.sqrt_nonneg H)])
    have hm := mul_le_mul hCK he (Real.exp_pos _).le hK.le
    exact ⟨hY.trans hm,fun M => (hM M).trans hm⟩
  · have hs : Real.sqrt H ≤ Real.sqrt R := Real.sqrt_le_sqrt (le_of_not_ge hRH)
    have he : Real.exp (-c*Real.sqrt R) ≤ Real.exp (-c*Real.sqrt H) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hprod : Real.exp (c*Real.sqrt R)*Real.exp (-c*Real.sqrt R)=1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hunit : 1 ≤ K*Real.exp (-c*Real.sqrt H) := by
      rw [← hprod]
      exact mul_le_mul hEK he (Real.exp_pos _).le hK.le
    exact ⟨measureReal_le_one.trans hunit,fun M => measureReal_le_one.trans hunit⟩

end NField.Alignment.CollisionUpperTails
