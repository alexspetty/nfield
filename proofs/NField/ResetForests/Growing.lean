/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Return
import NField.ResetForests.DivisorLog
/-! # The specified growing return window

The window is small compared with sqrt(log(log(p))). The logarithmic
divisor estimate is uniform in the actual return parameter, including
its fixed factors and every admitted return step.
-/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open Filter Asymptotics
open scoped Topology

def GrowingReturnWindow (L : ℕ → ℕ) : Prop :=
  (fun p : ℕ => (L p : ℝ)) =o[atTop]
    fun p => Real.sqrt (Real.log (Real.log (p : ℝ)))

theorem loglog_nat_tendsto :
    Tendsto (fun p : ℕ => Real.log (Real.log (p : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem window_square_ratio_tendsto {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    Tendsto (fun p => (L p : ℝ)^2/Real.log (Real.log (p : ℝ))) atTop (𝓝 0) := by
  have hs : Tendsto (fun p => ((L p : ℝ)/Real.sqrt (Real.log (Real.log (p : ℝ))))^2)
      atTop (𝓝 0) := by simpa using hL.tendsto_div_nhds_zero.pow 2
  apply hs.congr'
  filter_upwards [loglog_nat_tendsto.eventually (eventually_ge_atTop (0 : ℝ))] with p hp
  rw [div_pow, Real.sq_sqrt hp]

theorem window_height_ratio_tendsto {L : ℕ → ℕ} (hL : GrowingReturnWindow L) :
    Tendsto (fun p => (Real.log 15+5+2*(L p : ℝ)^2)/Real.log (Real.log (p : ℝ)))
      atTop (𝓝 0) := by
  have hc := loglog_nat_tendsto.const_div_atTop (Real.log 15+5)
  have hs := (window_square_ratio_tendsto hL).const_mul 2
  have hh := hc.add hs
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun p => by ring)

theorem growing_triple_divisor_subpower {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      (Core.tripleDivisorCount (returnDivisor p (L p)) : ℝ) ≤ (p : ℝ)^ε := by
  have hg : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : 0 < 16*Real.log 8 := by positivity
  have hr := (window_height_ratio_tendsto hL).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε/(16*Real.log 8) by positivity))
  filter_upwards [eventually_ge_atTop (3 : ℕ), hg.eventually (eventually_ge_atTop (4 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (4*Real.log 8)), hr] with p hp hX hY hr
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hD : 0 < returnDivisor p (L p) := return_divisor_pos hp _
  have hpD : (p : ℝ) ≤ returnDivisor p (L p) := by exact_mod_cast return_divisor_lower hp _
  have hlog : Real.log (p : ℝ) ≤ Real.log (returnDivisor p (L p) : ℝ) := Real.log_le_log hpR hpD
  have hloglog : Real.log (Real.log (p : ℝ)) ≤
      Real.log (Real.log (returnDivisor p (L p) : ℝ)) :=
    Real.log_le_log (by linarith) hlog
  have hYpos : 0 < Real.log (Real.log (p : ℝ)) := by
    have : 0 < Real.log 8 := Real.log_pos (by norm_num)
    linarith
  have hheight : Real.log (returnDivisor p (L p) : ℝ) ≤
      (Real.log 15+5+2*(L p : ℝ)^2)*Real.log (p : ℝ) := by
    have hh := return_divisor_log_height hp (L p)
    have h15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
    have hx : 1 ≤ Real.log (p : ℝ) := by linarith
    nlinarith
  have hb := triple_divisor_log_bound hD (hX.trans hlog) (hY.trans hloglog)
  have ht : Real.log (Core.tripleDivisorCount (returnDivisor p (L p)) : ℝ) ≤
      ε*Real.log (p : ℝ) := by
    calc
      _ ≤ (16*Real.log 8)*Real.log (returnDivisor p (L p) : ℝ)/
          Real.log (Real.log (returnDivisor p (L p) : ℝ)) := hb
      _ ≤ (16*Real.log 8)*Real.log (returnDivisor p (L p) : ℝ)/
          Real.log (Real.log (p : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) hYpos hloglog
      _ ≤ (16*Real.log 8)*((Real.log 15+5+2*(L p : ℝ)^2)*Real.log (p : ℝ))/
          Real.log (Real.log (p : ℝ)) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hheight hC.le) hYpos.le
      _ = ((16*Real.log 8)*((Real.log 15+5+2*(L p : ℝ)^2)/
          Real.log (Real.log (p : ℝ))))*Real.log (p : ℝ) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        simpa only [mul_comm] using ((lt_div_iff₀ hC).mp hr).le
  apply Real.le_rpow_of_log_le hpR ht

end NField.ResetForests.ReturnWindows
