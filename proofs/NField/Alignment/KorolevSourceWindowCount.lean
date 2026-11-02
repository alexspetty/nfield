/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevParameterCount
import NField.Alignment.KorolevSourceCoordinates

/-!
# Selected-window exclusion bounds in the source variables

The actual printed lower and upper conditions on x and m imply the
logarithmic range used in the uniform parameter proof. Both selected
prime families therefore have the missing-prime bound with the exact
source gamma. This supports Lemma A; it is not its squarefree assembly
or the bilinear/final incomplete Kloosterman estimate.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourceWindowCount
open Filter KorolevSourceScales KorolevParameterCount KorolevMissingPrimeCount
open scoped Topology Classical

def sourceGamma (C m x : ℝ) : ℝ :=
  (5*Real.log (Real.log x)-4*Real.log (Real.log m)-
    Real.log (Real.log (Real.log m))-Real.log C)/(24*Real.log (Real.log x))

def sourcePPrimes (C m x : ℝ) : Finset ℕ :=
  pPrimes (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)
def sourceQPrimes (C m x : ℝ) : Finset ℕ :=
  qPrimes (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)

theorem source_log_range {m x : ℝ} (hm : 0 < m) (hL : 1 < Real.log m)
    (hlo : Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x)
    (hhi : x ≤ m^(4/7 : ℝ)) :
    0 < x ∧ 0 < Real.log x ∧
      (4/5)*Real.log (Real.log m)+5*Real.log (Real.log (Real.log m)) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log m) := by
  have hL0 : 0 < Real.log m := by linarith
  have hv : 0 < Real.log (Real.log m) := Real.log_pos hL
  have hT : 0 < (Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5 := by positivity
  have hx : 0 < x := (Real.exp_pos _).trans_le hlo
  have hy := Real.log_le_log (Real.exp_pos _) hlo
  rw [Real.log_exp] at hy
  have hY : 0 < Real.log x := hT.trans_le hy
  have hh := Real.log_le_log hx hhi
  rw [Real.log_rpow hm] at hh
  refine ⟨hx, hY, ?_, Real.log_le_log hY (by linarith)⟩
  have hl := Real.log_le_log hT hy
  rw [Real.log_mul (by positivity : (Real.log m)^(4/5 : ℝ) ≠ 0)
    (by positivity : (Real.log (Real.log m))^5 ≠ 0),
    Real.log_rpow hL0, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  exact hl

theorem source_decay_identity {C m x : ℝ} (hx : 0 < Real.log x)
    (hu : Real.log (Real.log x) ≠ 0) :
    Real.exp (-gain (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)) =
      (Real.log x)^(-sourceGamma C m x) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  unfold gain sourceGamma
  field_simp

theorem eventual_source_window_counts (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        (((avoidSet x (sourcePPrimes C m x)).filter (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) ∧
        (((avoidSet x (sourceQPrimes C m x)).filter (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C m x) := by
  obtain ⟨K, hK, h⟩ := eventual_window_missing_counts (Real.log C) (Real.log_nonneg hC)
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine ⟨K, hK, ?_⟩
  filter_upwards [ht.eventually h, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1, ht.eventually_ge_atTop 2]
    with m hm hm0 hL hv2 x hlo hhi modulus
  dsimp only [Function.comp_apply] at hm hv2
  obtain ⟨hx, hY, hulo, hule⟩ := source_log_range hm0 hL hlo hhi
  have hw : 0 ≤ Real.log (Real.log (Real.log m)) := Real.log_nonneg (by linarith)
  have hu : 0 < Real.log (Real.log x) := by linarith
  have hh := hm _ hulo hule modulus
  rw [Real.exp_log hY, Real.exp_log hx,
    source_decay_identity hY hu.ne'] at hh
  exact hh


theorem source_gamma_coordinates (C m x : ℝ) (hu : Real.log (Real.log x) ≠ 0) :
    gain (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)/Real.log (Real.log x) =
      sourceGamma C m x := by
  unfold gain sourceGamma
  field_simp

theorem source_scale_correspondence (C m x : ℝ) (hL : 0 < Real.log m)
    (hY : 0 < Real.log x) (hu : Real.log (Real.log x) ≠ 0) :
    pStart (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (1/(2*(Real.log x/Real.log m)))*(Real.log x)^(2*sourceGamma C m x) ∧
    pStop (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (1/(2*(Real.log x/Real.log m)))*(Real.log x)^(4*sourceGamma C m x) ∧
    qStart (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (2/(Real.log x/Real.log m)^2)*(Real.log x)^(8*sourceGamma C m x) ∧
    qStop (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (2/(Real.log x/Real.log m)^2)*(Real.log x)^(10*sourceGamma C m x) := by
  have h := KorolevSourceCoordinates.scale_correspondence
    (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) hu
  rw [Real.exp_log hL, Real.exp_log hY, source_gamma_coordinates C m x hu] at h
  exact h

end NField.Alignment.KorolevSourceWindowCount
