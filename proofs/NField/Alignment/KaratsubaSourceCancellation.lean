/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceCost

/-! # Uniform bilinear cancellation on the paper's actual selected prime windows -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourceCancellation
open Filter KorolevPrimeWindows KorolevWindowMass KorolevSourceEnvelope
  KorolevWindowParameters KorolevSourceWindowDensity KorolevIndexSeparation
  KaratsubaSourceWindows KaratsubaSourceExponential KaratsubaSourceCost
open scoped Topology

/-- The full index envelope uniformly satisfies all three quadratic finite conditions. -/
theorem eventual_quadratic_conditions : ∀ᶠ v : ℝ in atTop,
    ∀ k : ℕ, (k : ℝ) ≤ envelope v →
      8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.exp v ∧
      16*lossConstant*(k : ℝ)^2 ≤ Real.exp v ∧ 36*(k : ℝ)^2 ≤ Real.exp v := by
  filter_upwards [eventual_envelope_small (8*(Real.log 4+1)),
    eventual_envelope_small (16*lossConstant), eventual_envelope_small 36]
    with v hs hf hq k hk
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
  have derive (K : ℝ) (hK : 0 ≤ K) (h : K*(envelope v)^2/Real.exp v ≤ 1) :
      K*(k : ℝ)^2 ≤ Real.exp v := by
    exact (mul_le_mul_of_nonneg_left hsq hK).trans
      (by simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos v)).mp h)
  refine ⟨?_, derive (16*lossConstant) (mul_nonneg (by norm_num) lossConstant_pos.le) hf,
    derive 36 (by norm_num) hq⟩
  have h := derive (8*(Real.log 4+1)) (by positivity) hs
  nlinarith only [h]

/-- Absorb the verified factorial/index cost into half the exponential saving. -/
theorem absorb_cost (L D : ℝ) (k s : ℕ) (hD : 0 ≤ D)
    (hc : cost k s ≤ Real.exp (L/(48*(k : ℝ)^2))) :
    cost k s*D*Real.exp (-L/(24*(k : ℝ)^2)) ≤ D*Real.exp (-L/(48*(k : ℝ)^2)) := by
  calc
    _ ≤ Real.exp (L/(48*(k : ℝ)^2))*D*Real.exp (-L/(24*(k : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hD) (Real.exp_pos _).le
    _ = D*Real.exp (L/(48*(k : ℝ)^2)+(-L/(24*(k : ℝ)^2))) := by rw [Real.exp_add]; ring
    _ = _ := by congr 2; ring

/-- All finite hypotheses and factorial losses are discharged uniformly over the source envelope. -/
theorem eventual_envelope_bound : ∀ᶠ v : ℝ in atTop,
    ∀ (m : ℕ) [NeZero m], Real.log m = Real.exp v → ∀ k s : ℕ,
      1 ≤ k → 1 ≤ s → (k : ℝ) ≤ envelope v → (s : ℝ) ≤ envelope v →
        8*(k : ℝ)^2 ≤ s → ∀ a b : ZMod m,
          (‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
            (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)))^(2*s*k) ≤
              (a.val.gcd m : ℝ)*Real.exp (-Real.log m/(48*(k : ℝ)^2)) := by
  filter_upwards [eventual_cost_absorbed, eventual_quadratic_conditions]
    with v hc hw m inst hcoord k s hk hs hke hse hsep a b
  have hK := hw k hke
  have hS := hw s hse
  rw [← hcoord] at hK hS
  have hcost := hc k s hk hs hsep hse
  rw [← hcoord] at hcost
  exact (normalized_exponential_bound hk hs hK.1 hK.2.1 hK.2.2 hS.1 hS.2.1 hS.2.2 hsep a b).trans
    (absorb_cost (Real.log m) (a.val.gcd m : ℝ) k s (Nat.cast_nonneg _) hcost)

/-- Uniform actual-window bilinear cancellation throughout the paper's original integer-modulus range. -/
theorem eventual_source_bilinear_power_bound (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in atTop,
    ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
        pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
        k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
        s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        ∀ a b : ZMod m,
          (‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
            (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)))^(2*s*k) ≤
              (a.val.gcd m : ℝ)*Real.exp (-Real.log m/(48*(k : ℝ)^2)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  have hc : 0 ≤ Real.log C := Real.log_nonneg hC
  filter_upwards [ht.eventually eventual_envelope_bound,
    ht.eventually (eventual_index_envelope (Real.log C) hc),
    ht.eventually (eventual_selected_index_separation (Real.log C) hc),
    ht.eventually (eventual_window_conditions (Real.log C) hc), hlog.eventually_gt_atTop 1]
    with m hv hi hsep hw hL inst x hlo hhi k s hkfirst hklast hsfirst hslast a b
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hw' := hw (Real.log (Real.log x)) hulo hule
  have hk := hw'.1.first_pos.trans hkfirst
  have hs := hw'.2.first_pos.trans hsfirst
  have hi' := hi (Real.log (Real.log x)) hulo hule
  have hke : (k : ℝ) ≤ envelope (Real.log (Real.log m)) := by
    have hh : (k : ℝ) ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) := by exact_mod_cast hklast
    dsimp only [Function.comp_apply] at hi'
    linarith [hi'.1]
  have hse : (s : ℝ) ≤ envelope (Real.log (Real.log m)) := by
    have hh : (s : ℝ) ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) := by exact_mod_cast hslast
    dsimp only [Function.comp_apply] at hi'
    linarith [hi'.2]
  have hseparate := hsep (Real.log (Real.log x)) hulo hule k s hklast hsfirst
  have hcoord : Real.log (m : ℝ) = Real.exp (Real.log (Real.log m)) :=
    (Real.exp_log (by linarith : 0 < Real.log (m : ℝ))).symm
  exact hv m hcoord k s hk hs hke hse hseparate a b

/-- Recover the ordinary norm estimate from the positive even power. -/
theorem ratio_le_exp_of_power_bound {z L : ℝ} {k s : ℕ} (hz : 0 ≤ z)
    (hk : 1 ≤ k) (hs : 1 ≤ s)
    (h : z^(2*s*k) ≤ Real.exp (-L/(48*(k : ℝ)^2))) :
    z ≤ Real.exp (-L/(96*(s : ℝ)*(k : ℝ)^3)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hp : Real.exp (-L/(96*(s : ℝ)*(k : ℝ)^3))^(2*s*k) =
      Real.exp (-L/(48*(k : ℝ)^2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hkR, ne_of_gt hsR]
    <;> ring
  have hn : 2*s*k ≠ 0 := Nat.ne_of_gt
    (Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) (by omega : 0 < s)) (by omega : 0 < k))
  apply (pow_le_pow_iff_left₀ hz (Real.exp_pos _).le hn).mp
  rw [hp]
  exact h

/-- The ordinary normalized bilinear norm decays uniformly for coprime frequencies on the actual source range. -/
theorem eventual_source_bilinear_bound (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in atTop,
    ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
        pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
        k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
        s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        ∀ a b : ZMod m, a.val.Coprime m →
          ‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
            (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)) ≤
              Real.exp (-Real.log m/(96*(s : ℝ)*(k : ℝ)^3)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventual_source_bilinear_power_bound C hC,
    ht.eventually (eventual_window_conditions (Real.log C) (Real.log_nonneg hC)),
    hlog.eventually_gt_atTop 1]
    with m hp hw hL inst x hlo hhi k s hkfirst hklast hsfirst hslast a b hacop
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hw' := hw (Real.log (Real.log x)) hulo hule
  have hk := hw'.1.first_pos.trans hkfirst
  have hs := hw'.2.first_pos.trans hsfirst
  apply ratio_le_exp_of_power_bound (div_nonneg (norm_nonneg _) (by positivity)) hk hs
  have hpow := hp x hlo hhi k s hkfirst hklast hsfirst hslast a b
  simpa only [hacop.gcd_eq_one, Nat.cast_one, one_mul] using hpow

end NField.Alignment.KaratsubaSourceCancellation
