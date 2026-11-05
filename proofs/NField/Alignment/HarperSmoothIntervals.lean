/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothCount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


/-!
# Smoothing finite sums over smooth integers

The real cutoff sums are measurable and integrable on each positive averaging
interval. Integrating the squared triangle inequality gives the normalized
smoothing bound, with its short-interval remainder retained. The remainder
support has at most 1 + x/(m*X) integers. These are the deterministic inputs
for the first smoothing step in Harper Section 3.4; no sieve bound is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothIntervals

open scoped BigOperators
open MeasureTheory HarperSmoothCount HarperSmoothDivisor

def smoothSum (x P : ℝ) (a : ℕ → ℂ) : ℂ := ∑ n ∈ smoothSet x P, a n

def smoothTail (u v P : ℝ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ (smoothSet v P).filter (fun n : ℕ => u < (n : ℝ)), a n

theorem smoothSet_filter_lower {u v P : ℝ} (huv : u ≤ v) :
    (smoothSet v P).filter (fun n : ℕ => (n : ℝ) ≤ u) = smoothSet u P := by
  ext n
  simp only [Finset.mem_filter, smoothSet_mem]
  constructor
  · rintro ⟨⟨hn, _, hs⟩, hnu⟩
    exact ⟨hn, hnu, hs⟩
  · rintro ⟨hn, hnu, hs⟩
    exact ⟨⟨hn, hnu.trans huv, hs⟩, hnu⟩

theorem smoothSum_split {u v P : ℝ} (huv : u ≤ v) (a : ℕ → ℂ) :
    smoothSum v P a = smoothSum u P a + smoothTail u v P a := by
  have h := Finset.sum_filter_add_sum_filter_not (smoothSet v P)
    (fun n : ℕ => (n : ℝ) ≤ u) a
  rw [smoothSet_filter_lower huv] at h
  simpa only [not_le, smoothSum, smoothTail] using h.symm

theorem smoothSum_measurable (P : ℝ) (a : ℕ → ℂ) :
    Measurable (fun x => smoothSum x P a) := by
  change Measurable ((fun N : ℕ => ∑ n ∈ (Finset.Ioc 0 N).filter
    (fun n => n ∈ smoothIntegers P), a n) ∘ Nat.floor)
  exact (measurable_of_countable _).comp Nat.measurable_floor

theorem smoothSum_square_split {u v P : ℝ} (huv : u ≤ v) (a : ℕ → ℂ) :
    ‖smoothSum v P a‖^2 ≤ 2*‖smoothSum u P a‖^2 + 2*‖smoothTail u v P a‖^2 := by
  rw [smoothSum_split huv a]
  calc
    _ ≤ (‖smoothSum u P a‖ + ‖smoothTail u v P a‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖smoothSum u P a‖ - ‖smoothTail u v P a‖)]

theorem quotient_square_split {x m t P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hmt : m ≤ t) (a : ℕ → ℂ) :
    ‖smoothSum (x/m) P a‖^2 ≤
      2*‖smoothSum (x/t) P a‖^2 + 2*‖smoothTail (x/t) (x/m) P a‖^2 :=
  smoothSum_square_split (div_le_div_of_nonneg_left hx hm hmt) a

theorem smoothTail_measurable (v P : ℝ) (a : ℕ → ℂ) :
    Measurable (fun u => smoothTail u v P a) := by
  simp only [smoothTail, Finset.sum_filter]
  exact Finset.measurable_sum _ (fun n _ =>
    measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)

theorem smoothSum_norm_le {u v P : ℝ} (huv : u ≤ v) (a : ℕ → ℂ) :
    ‖smoothSum u P a‖ ≤ ∑ n ∈ smoothSet v P, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [smoothSet_mem] at hn ⊢
    exact ⟨hn.1, hn.2.1.trans huv, hn.2.2⟩
  · intro n _ _
    exact norm_nonneg _

theorem smoothTail_norm_le (u v P : ℝ) (a : ℕ → ℂ) :
    ‖smoothTail u v P a‖ ≤ ∑ n ∈ smoothSet v P, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => norm_nonneg _)

theorem quotient_square_intervalIntegrable {x m b P : ℝ} (hx : 0 ≤ x)
    (hm : 0 < m) (hmb : m ≤ b) (a : ℕ → ℂ) :
    IntervalIntegrable (fun t => ‖smoothSum (x/t) P a‖^2) volume m b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hmb).2
  apply IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (((smoothSum_measurable P a).comp (measurable_const.div measurable_id)).norm.pow_const 2).aestronglyMeasurable
    ((∑ n ∈ smoothSet (x/m) P, ‖a n‖)^2)
  rw [ae_restrict_iff' measurableSet_Icc]
  apply Filter.Eventually.of_forall
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (smoothSum_norm_le (div_le_div_of_nonneg_left hx hm ht.1) a) 2

theorem tail_square_intervalIntegrable {x m b P : ℝ} (hmb : m ≤ b) (a : ℕ → ℂ) :
    IntervalIntegrable (fun t => ‖smoothTail (x/t) (x/m) P a‖^2) volume m b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hmb).2
  apply IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (((smoothTail_measurable (x/m) P a).comp (measurable_const.div measurable_id)).norm.pow_const 2).aestronglyMeasurable
    ((∑ n ∈ smoothSet (x/m) P, ‖a n‖)^2)
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (smoothTail_norm_le _ _ _ _) 2)

def smoothAverage (x P m X : ℝ) (a : ℕ → ℂ) : ℝ :=
  X/m * ∫ t in m..m*(1+1/X), ‖smoothSum (x/t) P a‖^2

def tailAverage (x P m X : ℝ) (a : ℕ → ℂ) : ℝ :=
  X/m * ∫ t in m..m*(1+1/X), ‖smoothTail (x/t) (x/m) P a‖^2

theorem smoothing_endpoint_le {m X : ℝ} (hm : 0 ≤ m) (hX : 0 < X) :
    m ≤ m*(1+1/X) := by
  nlinarith [one_div_pos.mpr hX]

theorem smoothing_normalization {m X : ℝ} (hm : 0 < m) (hX : 0 < X) :
    (X/m)*(m*(1+1/X)-m) = 1 := by
  field_simp
  ring

theorem smoothAverage_nonneg {m X : ℝ} (hm : 0 < m) (hX : 0 < X)
    (x P : ℝ) (a : ℕ → ℂ) : 0 ≤ smoothAverage x P m X a :=
  mul_nonneg (div_pos hX hm).le (intervalIntegral.integral_nonneg
    (smoothing_endpoint_le hm.le hX) (fun _ _ => sq_nonneg _))

theorem tailAverage_nonneg {m X : ℝ} (hm : 0 < m) (hX : 0 < X)
    (x P : ℝ) (a : ℕ → ℂ) : 0 ≤ tailAverage x P m X a :=
  mul_nonneg (div_pos hX hm).le (intervalIntegral.integral_nonneg
    (smoothing_endpoint_le hm.le hX) (fun _ _ => sq_nonneg _))

theorem smoothSum_smoothing {x m X P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (a : ℕ → ℂ) :
    ‖smoothSum (x/m) P a‖^2 ≤
      2*smoothAverage x P m X a + 2*tailAverage x P m X a := by
  have hmb := smoothing_endpoint_le hm.le hX
  have hmain := quotient_square_intervalIntegrable hx hm hmb (P := P) a
  have htail := tail_square_intervalIntegrable hmb (x := x) (P := P) a
  have hi := intervalIntegral.integral_mono_on hmb intervalIntegrable_const
    ((hmain.const_mul 2).add (htail.const_mul 2))
    (fun t ht => quotient_square_split hx hm ht.1 a)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hmain.const_mul 2) (htail.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have h := mul_le_mul_of_nonneg_left hi (div_pos hX hm).le
  rw [← mul_assoc, smoothing_normalization hm hX, one_mul] at h
  simpa only [smoothAverage, tailAverage, mul_add, mul_left_comm (X/m) 2] using h

theorem smoothTail_card_le {u v P : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (((smoothSet v P).filter (fun n : ℕ => u < (n : ℝ))).card : ℝ) ≤ 1+v-u := by
  have hs : (smoothSet v P).filter (fun n : ℕ => u < (n : ℝ)) ⊆
      Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnv, hnu⟩
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hu).mpr hnu,
      Nat.le_floor (smoothSet_mem.mp hnv).2.1⟩
  have hcard := Finset.card_le_card hs
  rw [Nat.card_Ioc] at hcard
  have hreal : (((smoothSet v P).filter (fun n : ℕ => u < (n : ℝ))).card : ℝ) ≤
      ((⌊v⌋₊ - ⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub (Nat.floor_mono huv)] at hreal
  linarith [Nat.floor_le (hu.trans huv), Nat.lt_floor_add_one u]

theorem smoothing_interval_width {x m X t : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (ht : t ∈ Set.Icc m (m*(1+1/X))) :
    x/m-x/t ≤ x/(m*X) := by
  have htpos : 0 < t := hm.trans_le ht.1
  have he : X*(m*(1+1/X)) = X*m+m := by field_simp
  have h := mul_le_mul_of_nonneg_left ht.2 hX.le
  rw [he] at h
  have hwidth : (t-m)*X ≤ t := by nlinarith [ht.1]
  apply (le_div_iff₀ (mul_pos hm hX)).mpr
  apply (mul_le_mul_iff_left₀ htpos).mp
  have heq : ((x/m-x/t)*(m*X))*t = x*((t-m)*X) := by field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hwidth hx

theorem quotient_tail_card_bound {x m X t P : ℝ} (hx : 0 ≤ x) (hm : 0 < m)
    (hX : 0 < X) (ht : t ∈ Set.Icc m (m*(1+1/X))) :
    (((smoothSet (x/m) P).filter (fun n : ℕ => x/t < (n : ℝ))).card : ℝ) ≤
      1+x/(m*X) := by
  have h := smoothTail_card_le (P := P) (div_nonneg hx (hm.le.trans ht.1))
    (div_le_div_of_nonneg_left hx hm ht.1)
  linarith [smoothing_interval_width hx hm hX ht]

theorem smoothSum_eq_fixed_support {u v P : ℝ} (huv : u ≤ v) (a : ℕ → ℂ) :
    smoothSum u P a =
      ∑ n ∈ smoothSet v P, if (n : ℝ) ≤ u then a n else 0 := by
  rw [smoothSum, ← smoothSet_filter_lower huv, Finset.sum_filter]

end NField.Alignment.HarperSmoothIntervals
