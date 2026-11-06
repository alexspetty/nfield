/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalDecay
import NField.Alignment.KorolevCanonicalInversePrefix

/-! # The actual inverse-residue prefix with its separate representation error -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSourcePrefixBound
open Filter KorolevSourceWindowCount KorolevCanonicalTuples
  KorolevCanonicalInversePrefix KorolevCanonicalSelectedSum
  DedekindReciprocity DedekindInverseResidueTransform
open scoped Topology BigOperators Classical

/-- The real canonical prefix and the complex tuple sum have the same norm. -/
theorem canonical_abs_eq_norm (P Q : Finset ℕ) (m r X : ℕ) :
    |canonicalPrefix P Q m r X| =
      ‖∑ t ∈ (tuples P Q ⌊Real.log (X : ℝ)⌋₊ X).filter (fun t => (value t).Coprime m),
        ((rationalSawtooth (r*inverseResidue (value t) m) m : ℚ) : ℂ)‖ := by
  have he : (canonicalPrefix P Q m r X : ℂ) =
      ∑ t ∈ (tuples P Q ⌊Real.log (X : ℝ)⌋₊ X).filter (fun t => (value t).Coprime m),
        ((rationalSawtooth (r*inverseResidue (value t) m) m : ℚ) : ℂ) := by
    unfold canonicalPrefix
    push_cast
    rfl
  rw [← he, Complex.norm_real, Real.norm_eq_abs]

/-- The full actual prefix is controlled by the canonical saving and its unmagnified failure error. -/
theorem eventual_source_prefix_bound (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, ∀ [NeZero m], ∀ X r : ℕ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ (X : ℝ) →
      (X : ℝ) ≤ (m : ℝ)^(4/7 : ℝ) → r.Coprime m →
      |inverseResiduePrefix m r X| ≤ (X : ℝ)/Real.log m +
        (K*(X : ℝ)*Real.log (Real.log X)*(Real.log X)^(-sourceGamma C m X))/2 := by
  obtain ⟨K, hK, hfail⟩ := eventual_failure_count C hC
  refine ⟨K, hK, ?_⟩
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  filter_upwards [KorolevCanonicalDecay.eventual_canonical_small C hC,
    hnat.eventually hfail,
    hnat.eventually (KorolevPrimeSeparation.eventual_source_prime_properties C hC),
    hlog.eventually_gt_atTop 1]
    with m hcan hf hp hL inst X r hlo hhi hr
  let P := sourcePPrimes C m X
  let Q := sourceQPrimes C m X
  have hXP : 0 < (X : ℝ) := (Real.exp_pos _).trans_le hlo
  have hX : 1 ≤ X := by exact_mod_cast (show (0 : ℝ) < X from hXP)
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hpp
    obtain ⟨k, _, _, hprime, _⟩ :=
      (KorolevPrimeWindows.selectedPrimes_mem _ _ _ _).mp hpp
    exact hprime
  have hQ : ∀ q ∈ Q, q.Prime := by
    intro q hqq
    exact (KorolevPrimeIntervals.intervalPrimes_mem.mp hqq).1
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hpp hpq
    have hh := hp (X : ℝ) hlo hhi p hpp p hpq
    exact (Nat.lt_irrefl p) hh.2.2.2
  have hcanonical : |canonicalPrefix P Q m r X| ≤ (X : ℝ)/Real.log m := by
    rw [canonical_abs_eq_norm]
    exact hcan (X : ℝ) hlo hhi ⌊Real.log (X : ℝ)⌋₊ X r hr
  have hrem := prefix_remainder_bound hP hQ hdis m r X
    (Nat.pos_of_ne_zero (NeZero.ne m)) hX
  have hfailure := hf (X : ℝ) hlo hhi m
  calc
    _ = |(inverseResiduePrefix m r X-canonicalPrefix P Q m r X)+canonicalPrefix P Q m r X| := by
      congr 1
      ring
    _ ≤ |inverseResiduePrefix m r X-canonicalPrefix P Q m r X|+|canonicalPrefix P Q m r X| :=
      abs_add_le _ _
    _ ≤ ((failure (X : ℝ) P Q m).card : ℝ)/2+(X : ℝ)/Real.log m := add_le_add hrem hcanonical
    _ ≤ _ := by linarith [hfailure]

end NField.Alignment.KorolevSourcePrefixBound
