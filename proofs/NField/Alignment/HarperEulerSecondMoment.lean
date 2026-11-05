/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact second moment of the actual random Euler product

Finite Steinhaus orthogonality and dominated convergence identify the
infinite product's second moment with the positive product at twice its
real part. On the critical line this is the reciprocal-prime product,
uniformly in frequency. Its logarithmic bound is already proved. Fubini
gives the exact expectation on every finite frequency interval, with all
joint and phase integrability obligations discharged.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperEulerSecondMoment

open scoped BigOperators Topology
open MeasureTheory Filter SteinhausMoment HarperSmoothDivisor HarperSmoothCount
  HarperRandomEulerProduct HarperEulerIntegral CollisionMertensInput

def partialEuler (P : ℝ) (s : ℂ) (N : ℕ) (ω : PhaseSpace) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), steinhaus n ω/(n : ℂ)^s

theorem partialEuler_measurable (P : ℝ) (s : ℂ) (N : ℕ) :
    Measurable (partialEuler P s N) :=
  Finset.measurable_sum _ (fun n _ => (steinhaus_measurable n).div_const _)

theorem partialEuler_tendsto (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    Tendsto (fun N => partialEuler P s N ω) atTop (𝓝 (eulerProduct P s ω)) := by
  have h := (smooth_LSeries_hasSum P hs ω).tendsto_sum_nat
  simpa only [smoothCoefficient_term, Set.indicator_apply, ← Finset.sum_filter, partialEuler] using h

theorem partialEuler_norm_bound (P : ℝ) {s : ℂ} (hs : 0 < s.re)
    (N : ℕ) (ω : PhaseSpace) : ‖partialEuler P s N ω‖ ≤ shiftedProduct P s.re := by
  calc
    _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), ‖steinhaus n ω/(n : ℂ)^s‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), (n : ℝ)^(-s.re) := by
      apply Finset.sum_congr rfl
      intro n hn
      simpa only [termHom, MonoidHom.coe_mk, OneHom.coe_mk, Complex.cpow_neg,
        ← div_eq_mul_inv] using termHom_norm (smoothIntegers_mem.mp (Finset.mem_filter.mp hn).2).1 s ω
    _ ≤ _ := smooth_partial_power_bound P hs _

theorem cpow_norm_sq {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ‖(n : ℂ)^(-s)‖^2 = (n : ℝ)^(-(2*s.re)) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  norm_num
  ring

theorem partialEuler_second_moment (P : ℝ) (s : ℂ) (N : ℕ) :
    (∫ ω, ‖partialEuler P s N ω‖^2 ∂phaseMeasure) =
      ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), (n : ℝ)^(-(2*s.re)) := by
  have hn : ∀ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), n ≠ 0 :=
    fun n h => (smoothIntegers_mem.mp (Finset.mem_filter.mp h).2).1
  have h := polynomial_second_moment ((Finset.range N).filter (· ∈ smoothIntegers P))
    (fun n => (n : ℂ)^(-s)) hn
  have he : (∫ ω, ‖partialEuler P s N ω‖^2 ∂phaseMeasure) =
      ∑ n ∈ (Finset.range N).filter (· ∈ smoothIntegers P), ‖(n : ℂ)^(-s)‖^2 := by
    simpa only [partialEuler, div_eq_mul_inv, Complex.cpow_neg, mul_comm] using h
  rw [he]
  exact Finset.sum_congr rfl (fun n hn' => cpow_norm_sq (hn n hn') s)

theorem partialEuler_energy_tendsto (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N => ∫ ω, ‖partialEuler P s N ω‖^2 ∂phaseMeasure) atTop
      (𝓝 (shiftedProduct P (2*s.re))) := by
  have h : HasSum ((fun n : ℕ => (n : ℝ)^(-(2*s.re))) ∘
      (Subtype.val : smoothIntegers P → ℕ)) (shiftedProduct P (2*s.re)) :=
    smooth_power_hasSum P (by positivity)
  rw [hasSum_subtype_iff_indicator] at h
  have ht := h.tendsto_sum_nat
  simpa only [Set.indicator_apply, ← Finset.sum_filter, partialEuler_second_moment] using ht

theorem eulerProduct_second_moment (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, ‖eulerProduct P s ω‖^2 ∂phaseMeasure) = shiftedProduct P (2*s.re) := by
  have hlim : Tendsto (fun N => ∫ ω, ‖partialEuler P s N ω‖^2 ∂phaseMeasure) atTop
      (𝓝 (∫ ω, ‖eulerProduct P s ω‖^2 ∂phaseMeasure)) := by
    apply tendsto_integral_filter_of_norm_le_const
      (Filter.Eventually.of_forall (fun N => ((partialEuler_measurable P s N).norm.pow_const 2).aestronglyMeasurable))
    · refine ⟨(shiftedProduct P s.re)^2, Filter.Eventually.of_forall (fun N => ?_)⟩
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (partialEuler_norm_bound P hs N ω) 2
    · exact Filter.Eventually.of_forall (fun ω => ((partialEuler_tendsto P hs ω).norm).pow 2)
  exact tendsto_nhds_unique hlim (partialEuler_energy_tendsto P hs)

theorem critical_second_moment (P t : ℝ) :
    (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) = shiftedProduct P 1 := by
  simpa only [linePoint_re, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0)] using
    eulerProduct_second_moment P (s := linePoint (1/2) t) (by norm_num [linePoint_re])

theorem shiftedProduct_one (P : ℝ) : shiftedProduct P 1 = inversePrimeProduct P := by
  simp [shiftedProduct, inversePrimeProduct, Real.rpow_neg_one]

theorem critical_second_moment_eq_inversePrimeProduct (P t : ℝ) :
    (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) = inversePrimeProduct P := by
  rw [critical_second_moment, shiftedProduct_one]

theorem eventual_second_moment_le_log : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ t : ℝ, (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^2 ∂phaseMeasure) ≤ C*Real.log P := by
  obtain ⟨C, hC, hb⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb.bound, eventually_ge_atTop (1 : ℝ)] with P hP hP1
  intro t
  rw [critical_second_moment_eq_inversePrimeProduct]
  simpa only [Real.norm_eq_abs, abs_of_pos (inversePrimeProduct_pos P),
    abs_of_nonneg (Real.log_nonneg hP1)] using hP

theorem eulerProduct_norm_sq_integrable (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun ω => ‖eulerProduct P s ω‖^2) phaseMeasure := by
  apply Integrable.of_bound ((eulerProduct_measurable P s).norm.pow_const 2).aestronglyMeasurable
    ((shiftedProduct P s.re)^2)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (eulerProduct_norm_le P hs ω) 2

def verticalEnergy (P sigma : ℝ) (z : ℝ × PhaseSpace) : ℝ :=
  ‖eulerProduct P (linePoint sigma z.1) z.2‖^2

def intervalEnergy (P sigma a b : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ t in Set.Ioc a b, verticalEnergy P sigma (t,ω)

theorem verticalEnergy_integrable (P a b : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    Integrable (verticalEnergy P sigma) ((volume.restrict (Set.Ioc a b)).prod phaseMeasure) := by
  apply Integrable.of_bound ((verticalProduct_measurable P sigma).norm.pow_const 2).aestronglyMeasurable
    ((shiftedProduct P sigma)^2)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := eulerProduct_norm_le P (s := linePoint sigma z.1) (by rwa [linePoint_re]) z.2
  rw [linePoint_re] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem intervalEnergy_integrable (P a b : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    Integrable (intervalEnergy P sigma a b) phaseMeasure :=
  (verticalEnergy_integrable P a b hs).integral_prod_right

theorem intervalEnergy_nonneg (P sigma a b : ℝ) (ω : PhaseSpace) :
    0 ≤ intervalEnergy P sigma a b ω := integral_nonneg (fun _ => sq_nonneg _)

theorem intervalEnergy_expectation (P : ℝ) {a b sigma : ℝ} (hs : 0 < sigma) (hab : a ≤ b) :
    (∫ ω, intervalEnergy P sigma a b ω ∂phaseMeasure) =
      (b-a)*shiftedProduct P (2*sigma) := by
  simp only [intervalEnergy]
  rw [← integral_integral_swap (f := fun t ω => verticalEnergy P sigma (t,ω))
    (verticalEnergy_integrable P a b hs)]
  have he (t : ℝ) : (∫ ω, verticalEnergy P sigma (t,ω) ∂phaseMeasure) =
      shiftedProduct P (2*sigma) := by
    simpa only [verticalEnergy, linePoint_re] using eulerProduct_second_moment P
      (s := linePoint sigma t) (by rwa [linePoint_re])
  simp_rw [he]
  simp [hab]

theorem unitEnergy_expectation (P v : ℝ) :
    (∫ ω, intervalEnergy P (1/2) (v-1/2) (v+1/2) ω ∂phaseMeasure) = inversePrimeProduct P := by
  rw [intervalEnergy_expectation P (by norm_num) (by linarith)]
  norm_num [shiftedProduct_one]

end NField.Alignment.HarperEulerSecondMoment
