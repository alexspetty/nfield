/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmLogLogScale
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Turning global upper bounds and attained sequences into exact limsups

Both halves are required explicitly. The boundedness hypotheses are proved
from a lower bound and the global upper estimates before limsup is used.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSharpLimsupTransfer

open Filter CollisionLogLogEnvelopes

theorem limsup_eq_of_upper_and_attained {f : ℕ → ℝ} {c : ℝ} {m : ℕ → ℕ}
    (hlower : ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, b ≤ f n)
    (hupper : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop, f n ≤ c+epsilon)
    (hm : Tendsto m atTop atTop) (hseq : Tendsto (f ∘ m) atTop (nhds c)) :
    limsup f atTop=c := by
  obtain ⟨b,hb⟩ := hlower
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) f :=
    isCoboundedUnder_le_of_eventually_le atTop hb
  have hbounded : atTop.IsBoundedUnder (· ≤ ·) f :=
    isBoundedUnder_of_eventually_le (hupper 1 (by norm_num))
  apply le_antisymm
  · by_contra h
    have he : 0 < (limsup f atTop-c)/2 := by linarith
    have hu := limsup_le_of_le hcob (hupper _ he)
    linarith
  · have hcobm : (map m atTop).IsCoboundedUnder (· ≤ ·) f :=
      isCoboundedUnder_le_of_eventually_le (map m atTop) (hm.eventually hb)
    have h := hm.limsup_comp_le_limsup hcobm hbounded
    rw [hseq.limsup_eq] at h
    exact h

theorem scaled_upper_to_ratio_upper {f s : ℕ → ℝ} {c : ℝ}
    (hs : ∀ᶠ n : ℕ in atTop, 0 < s n)
    (hupper : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop, f n ≤ (c+epsilon)*s n) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop, f n/s n ≤ c+epsilon := by
  intro epsilon hepsilon
  filter_upwards [hs,hupper epsilon hepsilon] with n hn hu
  exact (div_le_iff₀ hn).mpr hu

theorem loglog_square_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < (Real.log (Real.log n))^2 := by
  filter_upwards [loglog_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
  exact sq_pos_of_pos hn

end NField.Alignment.CollisionSharpLimsupTransfer
