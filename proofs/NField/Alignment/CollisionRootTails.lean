/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionUpperTails

/-!
# Exponential tails for the square root of the potential magnitude
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRootTails

open scoped Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionUpperTails

theorem root_tail_event {Ω : Type*} (F : Ω → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    {x | t < Real.sqrt |F x|}={x | t^2 < |F x|} := by
  ext x
  simpa only [Set.mem_setOf_eq,not_le] using
    not_congr (Real.sqrt_le_left (x := |F x|) ht)

theorem root_tail_normalize {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) {K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d)
    (hTail : ∀ H : ℝ, 1 ≤ H → μ.real {x | H < |F x|} ≤ K*Real.exp (-d*Real.sqrt H))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {x | t < Real.sqrt |F x|} ≤ (K+Real.exp d)*Real.exp (-d*t) := by
  by_cases ht1 : 1 ≤ t
  · rw [root_tail_event F ht]
    have hb := hTail (t^2) (by nlinarith)
    rw [Real.sqrt_sq ht] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos d]) (Real.exp_pos _).le)
  · have he : 1 ≤ Real.exp (d*(1-t)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hd.le (sub_nonneg.mpr (le_of_not_ge ht1)))
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ Real.exp (d*(1-t)) := he
      _ = Real.exp d*Real.exp (-d*t) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem potential_root_tails {d : ℝ} (hd : 0 < d) (hdπ : d < Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
      (phaseHaar.real {x | t < Real.sqrt |collisionPotential x|} ≤ K*Real.exp (-d*t)) ∧
      (∀ M : ℕ, phaseHaar.real {x | t < Real.sqrt |potentialMap collisionWeight M x|} ≤
        K*Real.exp (-d*t)) := by
  obtain ⟨K,hK,hTail⟩ := upper_tails hd hdπ
  refine ⟨K+Real.exp d,by positivity,?_⟩
  intro t ht
  exact ⟨root_tail_normalize phaseHaar collisionPotential hK.le hd (fun H hH => (hTail H hH).1) ht,
    fun M => root_tail_normalize phaseHaar (potentialMap collisionWeight M) hK.le hd
      (fun H hH => (hTail H hH).2 M) ht⟩

end NField.Alignment.CollisionRootTails
