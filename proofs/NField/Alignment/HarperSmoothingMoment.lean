/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothIntervals
import NField.Alignment.HarperProductApproximation
import Mathlib.MeasureTheory.Integral.Prod


/-!
# Random moments of the smoothing averages

Finite cutoff polynomials are jointly measurable and bounded on the product
of the averaging interval and the actual Steinhaus probability space.
Fubini therefore applies, with integrability established before each exchange.
The short-interval remainder has expectation at most 1 + x/(m*X) for unit-bounded
coefficients. Smoothing also holds under every nonnegative measurable box
weight of norm at most one. No rough-number sieve estimate is supplied here.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothingMoment

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperSmoothIntervals HarperSmoothCount

def intervalPolynomial (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (z : ℝ × PhaseSpace) : ℂ := ∑ n ∈ s, a z.1 n * steinhaus n z.2

theorem intervalPolynomial_measurable (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (ha : ∀ n ∈ s, Measurable (fun t => a t n)) : Measurable (intervalPolynomial s a) :=
  Finset.measurable_sum _ (fun n hn =>
    ((ha n hn).comp measurable_fst).mul ((steinhaus_measurable n).comp measurable_snd))

theorem intervalPolynomial_norm_le (s : Finset ℕ) (a : ℝ → ℕ → ℂ) (c : ℕ → ℝ)
    (hbound : ∀ t n, n ∈ s → ‖a t n‖ ≤ c n) (z : ℝ × PhaseSpace) :
    ‖intervalPolynomial s a z‖ ≤ ∑ n ∈ s, c n := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (steinhaus_norm_le n z.2)).trans
    (hbound z.1 n hn)

theorem intervalPolynomial_square_integrable (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (c : ℕ → ℝ) (ha : ∀ n ∈ s, Measurable (fun t => a t n))
    (hbound : ∀ t n, n ∈ s → ‖a t n‖ ≤ c n) (l r : ℝ) :
    Integrable (fun z => ‖intervalPolynomial s a z‖^2)
      ((volume.restrict (Set.Ioc l r)).prod phaseMeasure) := by
  apply Integrable.of_bound ((intervalPolynomial_measurable s a ha).norm.pow_const 2).aestronglyMeasurable
    ((∑ n ∈ s, c n)^2)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (intervalPolynomial_norm_le s a c hbound z) 2

theorem intervalPolynomial_average_integrable (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (c : ℕ → ℝ) (ha : ∀ n ∈ s, Measurable (fun t => a t n))
    (hbound : ∀ t n, n ∈ s → ‖a t n‖ ≤ c n) {l r : ℝ} (hlr : l ≤ r) :
    Integrable (fun ω => ∫ t in l..r, ‖intervalPolynomial s a (t,ω)‖^2) phaseMeasure := by
  simp_rw [intervalIntegral.integral_of_le hlr]
  exact (intervalPolynomial_square_integrable s a c ha hbound l r).integral_prod_right

theorem intervalPolynomial_second_moment (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (c : ℕ → ℝ) (ha : ∀ n ∈ s, Measurable (fun t => a t n))
    (hbound : ∀ t n, n ∈ s → ‖a t n‖ ≤ c n) (hs : ∀ n ∈ s, n ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ ω, (∫ t in l..r, ‖intervalPolynomial s a (t,ω)‖^2) ∂phaseMeasure) =
      ∫ t in l..r, ∑ n ∈ s, ‖a t n‖^2 := by
  simp_rw [intervalIntegral.integral_of_le hlr]
  rw [← integral_integral_swap (intervalPolynomial_square_integrable s a c ha hbound l r)]
  apply integral_congr_ae
  filter_upwards with t
  exact polynomial_second_moment s (a t) hs

def lowerCoefficient (x : ℝ) (w : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) ≤ x/t then w n else 0

def tailCoefficient (x : ℝ) (w : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if x/t < (n : ℝ) then w n else 0

theorem lowerCoefficient_measurable (x : ℝ) (w : ℕ → ℂ) (n : ℕ) :
    Measurable (fun t => lowerCoefficient x w t n) := by
  exact measurable_const.ite
    (measurableSet_le measurable_const (measurable_const.div measurable_id)) measurable_const

theorem tailCoefficient_measurable (x : ℝ) (w : ℕ → ℂ) (n : ℕ) :
    Measurable (fun t => tailCoefficient x w t n) := by
  exact measurable_const.ite
    (measurableSet_lt (measurable_const.div measurable_id) measurable_const) measurable_const

theorem lowerCoefficient_norm_le (x : ℝ) (w : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    ‖lowerCoefficient x w t n‖ ≤ ‖w n‖ := by
  unfold lowerCoefficient
  split_ifs
  · rfl
  · simp

theorem tailCoefficient_norm_le (x : ℝ) (w : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    ‖tailCoefficient x w t n‖ ≤ ‖w n‖ := by
  unfold tailCoefficient
  split_ifs
  · rfl
  · simp

theorem smoothSum_intervalPolynomial {x m t P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hmt : m ≤ t) (w : ℕ → ℂ) (ω : PhaseSpace) :
    smoothSum (x/t) P (fun n => w n * steinhaus n ω) =
      intervalPolynomial (smoothSet (x/m) P) (lowerCoefficient x w) (t,ω) := by
  rw [smoothSum_eq_fixed_support (div_le_div_of_nonneg_left hx hm hmt)]
  simp only [intervalPolynomial, lowerCoefficient, ite_mul, zero_mul]

theorem smoothTail_intervalPolynomial (x m t P : ℝ) (w : ℕ → ℂ) (ω : PhaseSpace) :
    smoothTail (x/t) (x/m) P (fun n => w n * steinhaus n ω) =
      intervalPolynomial (smoothSet (x/m) P) (tailCoefficient x w) (t,ω) := by
  simp only [smoothTail, intervalPolynomial, tailCoefficient, Finset.sum_filter, ite_mul, zero_mul]

theorem smoothAverage_integrable {x m X P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (w : ℕ → ℂ) :
    Integrable (fun ω => smoothAverage x P m X (fun n => w n * steinhaus n ω))
      phaseMeasure := by
  have hmb := smoothing_endpoint_le hm.le hX
  have heq (ω : PhaseSpace) :
      smoothAverage x P m X (fun n => w n * steinhaus n ω) =
      X/m * ∫ t in m..m*(1+1/X),
        ‖intervalPolynomial (smoothSet (x/m) P) (lowerCoefficient x w) (t,ω)‖^2 := by
    unfold smoothAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hmb] at ht
    dsimp only
    rw [smoothSum_intervalPolynomial hx hm ht.1]
  simp_rw [heq]
  exact (intervalPolynomial_average_integrable _ _ (fun n => ‖w n‖)
    (fun n _ => lowerCoefficient_measurable x w n)
    (fun t n _ => lowerCoefficient_norm_le x w t n) hmb).const_mul (X/m)

theorem tailAverage_integrable {m X : ℝ} (hm : 0 < m) (hX : 0 < X)
    (x P : ℝ) (w : ℕ → ℂ) :
    Integrable (fun ω => tailAverage x P m X (fun n => w n * steinhaus n ω))
      phaseMeasure := by
  simp_rw [tailAverage, smoothTail_intervalPolynomial]
  exact (intervalPolynomial_average_integrable _ _ (fun n => ‖w n‖)
    (fun n _ => tailCoefficient_measurable x w n)
    (fun t n _ => tailCoefficient_norm_le x w t n)
    (smoothing_endpoint_le hm.le hX)).const_mul (X/m)

theorem intervalPolynomial_energy_integrable (s : Finset ℕ) (a : ℝ → ℕ → ℂ)
    (c : ℕ → ℝ) (ha : ∀ n ∈ s, Measurable (fun t => a t n))
    (hbound : ∀ t n, n ∈ s → ‖a t n‖ ≤ c n) (hs : ∀ n ∈ s, n ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) :
    IntervalIntegrable (fun t => ∑ n ∈ s, ‖a t n‖^2) volume l r := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).2
  exact (intervalPolynomial_square_integrable s a c ha hbound l r).integral_prod_left.congr
    (Filter.Eventually.of_forall (fun t => polynomial_second_moment s (a t) hs))

theorem tailCoefficient_energy (s : Finset ℕ) (x t : ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ s, ‖tailCoefficient x w t n‖^2) =
      ∑ n ∈ s.filter (fun n : ℕ => x/t < (n : ℝ)), ‖w n‖^2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : x/t < (n : ℝ) <;> simp [tailCoefficient, hn]

theorem tailAverage_second_moment {m X : ℝ} (hm : 0 < m) (hX : 0 < X)
    (x P : ℝ) (w : ℕ → ℂ) :
    (∫ ω, tailAverage x P m X (fun n => w n * steinhaus n ω) ∂phaseMeasure) =
      X/m * ∫ t in m..m*(1+1/X),
        ∑ n ∈ (smoothSet (x/m) P).filter (fun n : ℕ => x/t < (n : ℝ)), ‖w n‖^2 := by
  simp_rw [tailAverage, smoothTail_intervalPolynomial]
  rw [integral_const_mul, intervalPolynomial_second_moment _ _ (fun n => ‖w n‖)
    (fun n _ => tailCoefficient_measurable x w n)
    (fun t n _ => tailCoefficient_norm_le x w t n)
    (fun n hn => Nat.ne_of_gt (smoothSet_mem.mp hn).1)
    (smoothing_endpoint_le hm.le hX)]
  simp_rw [tailCoefficient_energy]

theorem tailAverage_expectation_bound {x m X P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (w : ℕ → ℂ) (hw : ∀ n ∈ smoothSet (x/m) P, ‖w n‖ ≤ 1) :
    (∫ ω, tailAverage x P m X (fun n => w n * steinhaus n ω) ∂phaseMeasure) ≤
      1+x/(m*X) := by
  have hmb := smoothing_endpoint_le hm.le hX
  have hi := intervalPolynomial_energy_integrable (smoothSet (x/m) P)
    (tailCoefficient x w) (fun n => ‖w n‖)
    (fun n _ => tailCoefficient_measurable x w n)
    (fun t n _ => tailCoefficient_norm_le x w t n)
    (fun n hn => Nat.ne_of_gt (smoothSet_mem.mp hn).1) hmb
  have h := intervalIntegral.integral_mono_on hmb hi intervalIntegrable_const
    (g := fun _ => 1+x/(m*X)) (fun t ht => by
      rw [tailCoefficient_energy]
      calc
        _ ≤ ∑ n ∈ (smoothSet (x/m) P).filter (fun n : ℕ => x/t < (n : ℝ)), (1 : ℝ) :=
          Finset.sum_le_sum (fun n hn => pow_le_one₀ (norm_nonneg _)
            (hw n (Finset.mem_filter.mp hn).1))
        _ = _ := by simp
        _ ≤ _ := quotient_tail_card_bound (P := P) hx hm hX ht)
  have hb := mul_le_mul_of_nonneg_left h (div_pos hX hm).le
  rw [intervalIntegral.integral_const, smul_eq_mul, ← mul_assoc,
    smoothing_normalization hm hX, one_mul] at hb
  rw [tailAverage_second_moment hm hX]
  simpa only [tailCoefficient_energy] using hb

theorem weighted_smooth_smoothing {x m X P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (w : ℕ → ℂ) (W : PhaseSpace → ℝ)
    (hW : Measurable W) (hWnonneg : ∀ ω, 0 ≤ W ω) (hWbound : ∀ ω, ‖W ω‖ ≤ 1) :
    (∫ ω, ‖smoothSum (x/m) P (fun n => w n * steinhaus n ω)‖^2 * W ω ∂phaseMeasure) ≤
      2*(∫ ω, smoothAverage x P m X (fun n => w n * steinhaus n ω) * W ω ∂phaseMeasure) +
      2*(∫ ω, tailAverage x P m X (fun n => w n * steinhaus n ω) * W ω ∂phaseMeasure) := by
  have hmain := (smoothAverage_integrable hx hm hX (P := P) w).mul_bdd
    hW.aestronglyMeasurable (Filter.Eventually.of_forall hWbound)
  have htail := (tailAverage_integrable hm hX x P w).mul_bdd
    hW.aestronglyMeasurable (Filter.Eventually.of_forall hWbound)
  have hleft : Integrable
      (fun ω => ‖smoothSum (x/m) P (fun n => w n * steinhaus n ω)‖^2 * W ω) phaseMeasure :=
    (HarperMomentExpansion.grouped_norm_sq_integrable (smoothSet (x/m) P) id w).mul_bdd
      hW.aestronglyMeasurable (Filter.Eventually.of_forall hWbound)
  calc
    _ ≤ ∫ ω, 2*(smoothAverage x P m X (fun n => w n * steinhaus n ω)*W ω) +
        2*(tailAverage x P m X (fun n => w n * steinhaus n ω)*W ω) ∂phaseMeasure := by
      apply integral_mono hleft ((hmain.const_mul 2).add (htail.const_mul 2))
      intro ω
      have h := mul_le_mul_of_nonneg_right (smoothSum_smoothing (P := P) hx hm hX
        (fun n => w n * steinhaus n ω)) (hWnonneg ω)
      simpa only [add_mul, mul_assoc, Pi.add_apply] using h
    _ = _ := by
      rw [integral_add (hmain.const_mul 2) (htail.const_mul 2),
        integral_const_mul, integral_const_mul]

end NField.Alignment.HarperSmoothingMoment
