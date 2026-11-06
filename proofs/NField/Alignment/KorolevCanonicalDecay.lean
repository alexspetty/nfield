/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalTupleBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Absorbing the full canonical summation cost into cubic logarithmic decay -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalDecay
open Filter KorolevSourceWindowCount KorolevCanonicalTuples
  DedekindReciprocity DedekindInverseResidueTransform
open scoped Topology BigOperators Classical

/-- Cubic log-log decay absorbs the complete polynomial population and harmonic costs. -/
theorem eventual_absorption (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ v : ℝ in atTop,
    C*(Real.exp v)^6*v^12*Real.exp (-v^3/128) ≤ 1/Real.exp v := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (32 : ℝ)] with v hs hv
  have hv0 : 0 ≤ v := by linarith
  have hsquare : (1024 : ℝ) ≤ v^2 := by nlinarith
  have hcube : 1024*v ≤ v^3 := by
    have hh := mul_le_mul_of_nonneg_right hsquare hv0
    nlinarith only [hh]
  have he : 7*v-v^3/128 ≤ -v := by nlinarith only [hcube]
  have hid : (Real.exp v)^6*Real.exp (-v^3/128)*Real.exp v =
      Real.exp (7*v-v^3/128) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  apply (le_div_iff₀ (Real.exp_pos v)).mpr
  calc
    _ = C*v^12*((Real.exp v)^6*Real.exp (-v^3/128)*Real.exp v) := by ring
    _ = C*v^12*Real.exp (7*v-v^3/128) := by rw [hid]
    _ ≤ C*v^12*Real.exp (-v) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ ≤ 1 := by simpa only [mul_assoc] using hs

/-- The complete canonical tuple contribution is eventually bounded by X/log m. -/
theorem eventual_canonical_small (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ B X r : ℕ, r.Coprime m →
      ‖∑ t ∈ (tuples (sourcePPrimes C m x) (sourceQPrimes C m x) B X).filter
        (fun t => (value t).Coprime m),
        ((rationalSawtooth (r*inverseResidue (value t) m) m : ℚ) : ℂ)‖ ≤
          (X : ℝ)/Real.log m := by
  let A := max 1 (8*KorolevPrimeIntervals.errorConstant)
  have hA : 1 ≤ A := le_max_left _ _
  have herror : 8*KorolevPrimeIntervals.errorConstant ≤ A := le_max_right _ _
  obtain ⟨K, hK, hb⟩ := KorolevCanonicalTupleBound.eventual_canonical_tuple_bound C hC A hA herror
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hb, ht.eventually (eventual_absorption (12*K*Real.exp (4*A)) (by positivity)),
    hlog.eventually_ge_atTop 1] with m hb hs hL inst x hlo hhi B X r hr
  have hbound := hb x hlo hhi B X r hr
  have hH0 : 0 ≤ (harmonic m : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic m := by unfold harmonic; positivity
    exact_mod_cast hQ
  have hH : (harmonic m : ℝ) ≤ 2*Real.log m := by
    have hh := harmonic_le_one_add_log m
    linarith
  have hH1 : 1+(harmonic m : ℝ) ≤ 3*Real.log m := by linarith
  have hpair : (1+(harmonic m : ℝ))*(harmonic m : ℝ) ≤ 6*(Real.log m)^2 := by
    have hh := mul_le_mul hH1 hH hH0 (by positivity : 0 ≤ 3*Real.log (m : ℝ))
    nlinarith only [hh]
  dsimp only [Function.comp_apply] at hs
  rw [Real.exp_log (by linarith : 0 < Real.log (m : ℝ))] at hs
  calc
    _ ≤ 2*K*(1+(harmonic m : ℝ))*(harmonic m : ℝ)*(Real.log (Real.log m))^12*
        Real.exp (-(Real.log (Real.log m))^3/128)*Real.exp (4*A)*(X : ℝ)*(Real.log m)^4 := hbound
    _ = (2*K*(Real.log (Real.log m))^12*Real.exp (-(Real.log (Real.log m))^3/128)*
        Real.exp (4*A)*(X : ℝ)*(Real.log m)^4)*((1+(harmonic m : ℝ))*(harmonic m : ℝ)) := by ring
    _ ≤ (2*K*(Real.log (Real.log m))^12*Real.exp (-(Real.log (Real.log m))^3/128)*
        Real.exp (4*A)*(X : ℝ)*(Real.log m)^4)*(6*(Real.log m)^2) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = (X : ℝ)*((12*K*Real.exp (4*A))*(Real.log m)^6*(Real.log (Real.log m))^12*
        Real.exp (-(Real.log (Real.log m))^3/128)) := by ring
    _ ≤ (X : ℝ)*(1/Real.log m) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg X)
    _ = _ := by ring

end NField.Alignment.KorolevCanonicalDecay
