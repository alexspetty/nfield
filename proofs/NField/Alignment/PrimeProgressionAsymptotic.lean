/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.External.ProgressionPNT.Wiener

/-! # The prime-progression input from Mathlib's Dirichlet boundary

Mathlib proves the residue-class Dirichlet series, its simple pole, and the
continuous remainder on the closed half-plane. The proved Wiener-Ikehara
theorem turns those actual functions into an ordinary partial-sum limit.
-/

noncomputable section
namespace NField.Alignment.PrimeProgressionAsymptotic

open scoped BigOperators Topology
open Filter ArithmeticFunction

theorem residueClass_cheby {q : ℕ} (a : ZMod q) :
    cheby (fun n => (vonMangoldt.residueClass a n : ℂ)) := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => ?_⟩
  apply le_trans _ (hC N)
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  exact vonMangoldt.residueClass_le a n

theorem residueClass_summable_nterm {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hbase : Summable (nterm (fun n => (vonMangoldt n : ℂ)) σ) := by
    simpa only [← nterm_eq_norm_term] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ).norm
  apply hbase.of_nonneg_of_le
  · intro n
    unfold nterm
    split_ifs <;> positivity
  · intro n
    unfold nterm
    split_ifs
    · rfl
    · rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldt.residueClass_nonneg a n),
        Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      exact div_le_div_of_nonneg_right (vonMangoldt.residueClass_le a n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- Title: `Prime progression von Mangoldt density`.
The residue class is reduced, the modulus is any fixed positive integer,
and the limit is the ordinary ordered sum over integers below the cutoff. -/
theorem residueClass_partial_sum_tendsto {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, vonMangoldt.residueClass a n) / (N : ℝ))
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (f := vonMangoldt.residueClass a)
    (G := vonMangoldt.LFunctionResidueClassAux a)
  · exact fun n => vonMangoldt.residueClass_nonneg a n
  · exact fun σ hσ => residueClass_summable_nterm a hσ
  · exact residueClass_cheby a
  · exact vonMangoldt.continuousOn_LFunctionResidueClassAux a
  · simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      vonMangoldt.eqOn_LFunctionResidueClassAux ha

end NField.Alignment.PrimeProgressionAsymptotic

#print axioms WienerIkeharaTheorem'
#print axioms WeakPNT
#print axioms NField.Alignment.PrimeProgressionAsymptotic.residueClass_partial_sum_tendsto
