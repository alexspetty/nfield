/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSourceScales
import NField.Alignment.KorolevSourceEnvelope

/-!
# Discharging the finite conditions for the actual rounded windows

For fixed c>=0 and all sufficiently large v, uniformly over the source
logarithmic range, both selected families satisfy their finite size,
cutoff and mass-error conditions. The final q index follows its defining
endpoint inequality rather than an unverified extracted rounding bound.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevWindowParameters
open Filter KorolevEndpointIndices KorolevSourceScales KorolevSourceEnvelope
  KorolevPrimeWindows KorolevWindowMass
open scoped Topology BigOperators

def pFirst (v u c : ℝ) : ℕ := lowerIndex (pStart v u c)
def pLast (v u c : ℝ) : ℕ := upperIndex (pStop v u c) 1
def qFirst (v u c : ℝ) : ℕ := lowerIndex (qStart v u c)
def qLast (v u c : ℝ) : ℕ := upperIndex (qStop v u c) 0

structure WindowConditions (L Q g : ℝ) (a b : ℕ) : Prop where
  first_pos : 1 ≤ a
  ordered : a ≤ b
  size : 8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L
  cutoff : upperEndpoint L a ≤ Q
  squared_error : lossConstant*((b : ℝ)+1)^2/L ≤ 1
  linear_error : 12*KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/L ≤ 1
  log_gain : 2*g-Real.log 4 ≤ Real.log ((b : ℝ)+1)-Real.log a

theorem rounded_log_gain {A B g : ℝ} (hA : 2 ≤ A)
    (hR : 4 ≤ Real.exp (2*g)) (heq : B = A*Real.exp (2*g))
    {offset : ℕ} (ho : offset ≤ 1) :
    2*g-Real.log 4 ≤ Real.log ((upperIndex B offset : ℝ)+1)-Real.log (lowerIndex A) := by
  have hA0 : 0 < A := by linarith
  have hB : 4*A ≤ B := by rw [heq]; nlinarith [mul_le_mul_of_nonneg_left hR hA0.le]
  have hp := rounded_pair_bounds hA hB ho
  have ha0 : (0 : ℝ) < lowerIndex A := by exact_mod_cast (Nat.zero_lt_of_lt hp.1)
  have hB0 : 0 < B := by linarith
  have hla := Real.log_le_log ha0 hp.2.2.1
  have hlb := Real.log_le_log (by positivity : 0 < B/2) hp.2.2.2.1
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hA0.ne'] at hla
  rw [Real.log_div hB0.ne' (by norm_num : (2 : ℝ) ≠ 0), heq,
    Real.log_mul hA0.ne' (Real.exp_ne_zero _), Real.log_exp] at hlb
  rw [← heq] at hlb
  have h4 : Real.log 4 = Real.log 2+Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  linarith

theorem conditions_of_scales {v u g A B t : ℝ} (hA : 2 ≤ A)
    (hR : 4 ≤ Real.exp (2*g)) (heq : B = A*Real.exp (2*g))
    (hBenv : 2*B ≤ envelope v) (ht : 0 < t)
    (hAt : Real.exp v/(2*t) = A) (hcut : t ≤ Real.exp u/u)
    (hfinite : ∀ b : ℕ, (b : ℝ)+1 ≤ envelope v →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ Real.exp v ∧
      lossConstant*((b : ℝ)+1)^2/Real.exp v ≤ 1 ∧
      12*KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/Real.exp v ≤ 1)
    {offset : ℕ} (ho : offset ≤ 1) :
    WindowConditions (Real.exp v) (Real.exp (Real.exp u/u)) g
      (lowerIndex A) (upperIndex B offset) := by
  have hB : 4*A ≤ B := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ A by linarith)]
  have hp := rounded_pair_bounds hA hB ho
  have hf := hfinite (upperIndex B offset) (hp.2.2.2.2.trans hBenv)
  have he := (lowerIndex_endpoint ht hA hAt).1
  have hx := Real.exp_le_exp.mpr hcut
  refine ⟨hp.1, hp.2.1, hf.1, ?_, hf.2.1, hf.2.2, rounded_log_gain hA hR heq ho⟩
  exact he.trans (by linarith [Real.exp_pos t])

theorem eventual_window_conditions (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      WindowConditions (Real.exp v) (Real.exp (Real.exp u/u)) (gain v u c)
        (pFirst v u c) (pLast v u c) ∧
      WindowConditions (Real.exp v) (Real.exp (Real.exp u/u)) (gain v u c)
        (qFirst v u c) (qLast v u c) := by
  filter_upwards [eventual_scale_bounds c hc, eventual_finite_conditions]
    with v hv hf u hulo hule
  obtain ⟨hu, hg, hpA, hqA, hR, hRu, hpB, hqB⟩ := hv u hulo hule
  have ht := threshold_cutoff_bounds hu hule hg (by linarith)
  constructor
  · exact conditions_of_scales hpA hR (pStop_ratio v u c)
      (by unfold envelope; linarith) (Real.exp_pos _) (pStart_threshold v u c) ht.1 hf (by norm_num)
  · exact conditions_of_scales hqA hR (qStop_ratio v u c)
      (by unfold envelope; linarith) (by unfold qThreshold; positivity)
      (qStart_threshold v u c) ht.2 hf (by norm_num)

theorem eventual_source_mass_bounds (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      gain v u c-Real.log 4/2-1 ≤
        ∑ p ∈ selectedPrimes (Real.exp v) (pFirst v u c) (pLast v u c), (1 : ℝ)/p ∧
      2*gain v u c-Real.log 4-1 ≤
        ∑ p ∈ KorolevPrimeIntervals.intervalPrimes
          (upperEndpoint (Real.exp v) (qLast v u c+1))
          (upperEndpoint (Real.exp v) (qFirst v u c)), (1 : ℝ)/p := by
  filter_upwards [eventual_window_conditions c hc] with v hv u hulo hule
  obtain ⟨hp, hq⟩ := hv u hulo hule
  constructor
  · have hm := selected_mass_lower hp.first_pos hp.ordered hp.size
    have he := hp.squared_error
    have hg := hp.log_gain
    linarith
  · have hm := contiguous_mass_lower hq.first_pos hq.ordered hq.size
    have he := hq.linear_error
    have hg := hq.log_gain
    linarith

end NField.Alignment.KorolevWindowParameters
