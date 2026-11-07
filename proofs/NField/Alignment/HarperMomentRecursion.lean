/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperNormalizedEnergy

/-!
# The critical fractional-moment recursion

The next exponent is (1+q)/2. Both event contributions use the same good
event, with probability and restricted-moment bounds proved for that event.

-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperMomentRecursion
open Filter MeasureTheory SteinhausMoment HarperPrimeBlocks HarperCriticalGoodEvent
  HarperGoodEventCutoff HarperNormalizedEnergy HarperFractionalEventSplit

def nextExponent (q : ℝ) : ℝ := (1+q)/2

theorem nextExponent_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < nextExponent q ∧ q < nextExponent q ∧ nextExponent q < 1 := by
  unfold nextExponent
  exact ⟨by linarith,by linarith,by linarith⟩

theorem interpolationExponent_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < q/nextExponent q ∧ q/nextExponent q < 1 := by
  have h := nextExponent_bounds hq0.le hq1
  exact ⟨div_pos hq0 h.1,(div_lt_one h.1).mpr h.2.1⟩

theorem actual_normalized_recursion :
    ∃ K C D : ℝ, 0 < K ∧ 0 < C ∧ 0 < D ∧ ∀ᶠ x : ℝ in atTop,
      1 < sourceCutoff x ∧ 0 < Real.sqrt (Real.log (Real.log x)) ∧
      ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 →
        0 ≤ normalizedMoment (sourceCutoff x) K q ∧ normalizedMoment (sourceCutoff x) K q ≤ 1 ∧
        (q < 1 → ∀ a : ℝ, 1 ≤ a →
          normalizedMoment (sourceCutoff x) K q ≤
            (C*min 1 (a/Real.sqrt (Real.log (Real.log x))))^q+
            (normalizedMoment (sourceCutoff x) K (nextExponent q))^(q/nextExponent q)*
              (D*Real.exp (-2*a))^(1-q/nextExponent q)) := by
  obtain ⟨B,K,C,D,hK,hC,hD,hbound⟩ := joint_normalized_bounds
  refine ⟨K,C,D,hK,hC,hD,?_⟩
  filter_upwards [hbound] with x hx
  rcases hx with ⟨hP,hs,hmean,hgood⟩
  refine ⟨hP,hs,fun q hq0 hq1 => ?_⟩
  have hq : 0 < q := by linarith
  refine ⟨normalizedMoment_nonneg hP.le hK.le q,
    normalizedMoment_le_one hP.le hK.le hmean hq.le hq1,?_⟩
  intro hq1' a ha
  have hr := nextExponent_bounds hq.le hq1'
  have ht := interpolationExponent_bounds hq hq1'
  have hG := sourceGoodEvent_measurable x (terminalBlock B x) a
  have hn := normalizedEnergy_nonneg hP.le hK.le
  have hsplit := fractional_event_split (normalizedEnergy_integrable (sourceCutoff x) K) hn
    (normalizedEnergy_bound hP hK) hG hq hr.2.1 hr.2.2.le
  have hg := hgood a ha q hq.le hq1
  apply hsplit.trans
  apply add_le_add hg.1
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow (measureReal_nonneg) hg.2 (by linarith)
  · exact Real.rpow_nonneg (normalizedMoment_nonneg hP.le hK.le _) _

end NField.Alignment.HarperMomentRecursion
