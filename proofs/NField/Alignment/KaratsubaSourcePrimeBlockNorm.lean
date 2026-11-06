/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourcePrimeBlocks

/-! # Ordinary block norm saving with the exact frequency-gcd root retained -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourcePrimeBlockNorm
open Filter KorolevPrimeWindows KorolevLogarithmicPartition KorolevWindowParameters
  KaratsubaSourcePrimeBlocks
open scoped Topology

/-- The positive even root preserves the nonunit-frequency gcd factor. -/
theorem ratio_le_gcd_root_exp {z D L : ℝ} {k s : ℕ} (hz : 0 ≤ z) (hD : 0 ≤ D)
    (hk : 1 ≤ k) (hs : 1 ≤ s)
    (h : z^(2*s*k) ≤ D*Real.exp (-L/(128*(k : ℝ)^2))) :
    z ≤ D^(((2*s*k : ℕ) : ℝ)⁻¹)*Real.exp (-L/(256*(s : ℝ)*(k : ℝ)^3)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hn : 2*s*k ≠ 0 := Nat.ne_of_gt (by positivity : 0 < 2*s*k)
  have hg : (D^(((2*s*k : ℕ) : ℝ)⁻¹))^(2*s*k) = D := Real.rpow_inv_natCast_pow hD hn
  have he : Real.exp (-L/(256*(s : ℝ)*(k : ℝ)^3))^(2*s*k) =
      Real.exp (-L/(128*(k : ℝ)^2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hkR, ne_of_gt hsR]
    <;> ring
  apply (pow_le_pow_iff_left₀ hz (by positivity) hn).mp
  rw [mul_pow, hg, he]
  exact h

/-- Actual source blocks have ordinary norm decay, including the exact root of every frequency gcd. -/
theorem eventual_source_block_bound (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      k ≤ pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      s ≤ qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
      ∀ lp lq Dp Dq : ℝ, 1 ≤ lp → 1 ≤ lq → A ≤ Dp → A ≤ Dq →
      Real.exp lp = lowerEndpoint (Real.log m) k →
      Real.exp lq = upperEndpoint (Real.log m) (s+1) →
      Real.exp (lp+Dp) = upperEndpoint (Real.log m) k →
      Real.exp (lq+Dq) = upperEndpoint (Real.log m) s →
      ∀ i j : ℕ, i < blockCount Dp A → j < blockCount Dq A →
      ∀ P₀ Q₀ : Finset ℕ, P₀ ⊆ coprimeBlock m lp Dp A i → Q₀ ⊆ coprimeBlock m lq Dq A j →
      ∀ a b : ZMod m,
      ‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
        (((coprimeBlock m lp Dp A i).card : ℝ)*((coprimeBlock m lq Dq A j).card : ℝ)) ≤
          (a.val.gcd m : ℝ)^(((2*s*k : ℕ) : ℝ)⁻¹)*
            Real.exp (-Real.log m/(256*(s : ℝ)*(k : ℝ)^3)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventual_source_block_power_bound C hC A hA herror,
    ht.eventually (KorolevUncutPrimeRectangle.eventual_first_indices_ge_two (Real.log C) (Real.log_nonneg hC)),
    hlog.eventually_gt_atTop 1]
    with m hp hf hL inst x hlo hhi k s hkfirst hklast hsfirst hslast
      lp lq Dp Dq hlp hlq hDp hDq hLp hLq hUp hUq i j hi hj P₀ Q₀ hPsub hQsub a b
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hh := hf (Real.log (Real.log x)) hulo hule
  dsimp only [Function.comp_apply] at hh
  have hk : 1 ≤ k := by omega
  have hs : 1 ≤ s := by omega
  apply ratio_le_gcd_root_exp (div_nonneg (norm_nonneg _) (by positivity)) (Nat.cast_nonneg _) hk hs
  exact hp x hlo hhi k s hkfirst hklast hsfirst hslast lp lq Dp Dq hlp hlq hDp hDq
    hLp hLq hUp hUq i j hi hj P₀ Q₀ hPsub hQsub a b

end NField.Alignment.KaratsubaSourcePrimeBlockNorm
