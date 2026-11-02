/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperAverageApproximation

/-!
# Smooth character/random comparison with an explicit error sum

At the actual rounded cutoff and Taylor order, the unit and complete-size
conditions hold for every subset order. The exact Taylor comparison and
the proved remainder estimates bound the difference of the actual smooth
averages. Coefficient norms at most one supply the finite prime-energy bound.
The remaining analytic task is to estimate the explicit binomial error sum.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothComparison

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperPrimeProductMoment HarperRemainderProduct
  HarperProductApproximation HarperAverageApproximation HarperPrimeTaylorComparison
  HarperTaylorBudget HarperRoundedCutoff MagnitudeShortComparison
  SpectralRepulsion CollisionMertensInput CollisionCharacterStructure

theorem abs_sub_le_of_middle_eq {a b c d R : ℝ}
    (ha : |a - b| ≤ R) (hc : |c - d| ≤ R) (he : b = d) : |a - c| ≤ 2 * R := by
  calc
    _ ≤ |a - b| + |b - c| := abs_sub_le a b c
    _ ≤ R + R := add_le_add ha (by rw [he, abs_sub_comm]; exact hc)
    _ = _ := by ring

theorem eventual_comparison_data : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    p.Prime → 0 < taylorOrder x ∧
      (∀ n ∈ Finset.Icc 1 (p - 1), 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime (p ^ 2)) ∧
      (∀ r ∈ primesUpTo P, r.Coprime (p ^ 2)) ∧
      (∀ j ≤ factorCount x, x * (P ^ 2) ^ (taylorOrder x * j) < (p ^ 2 : ℕ)) ∧
      (∀ j ≤ factorCount x, (P ^ 2) ^ (taylorOrder x * j) < (p ^ 2 : ℕ)) := by
  filter_upwards [eventual_prime_square_remainder_size,
    base_minus_one_tendsto.eventually eventual_cutoff_square_lt,
    base_minus_one_tendsto.eventually eventual_taylor_data] with p hb hsmall ht
  dsimp only at hb ⊢
  intro hp
  have hsize : ∀ j ≤ factorCount ((p : ℝ) - 1),
      ((p : ℝ) - 1) * (primeCutoff ((p : ℝ) - 1) ^ 2) ^ (taylorOrder ((p : ℝ) - 1) * j) <
        (p ^ 2 : ℕ) := by
    intro j hj
    have h := hb j hj
    simpa only [Real.rpow_natCast, Nat.cast_pow] using h.1.trans_lt (h.2.1.trans h.2.2)
  refine ⟨ht.2.2.1, ?_, ?_, hsize, ?_⟩
  · intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    have hnxR : (n : ℝ) ≤ (p : ℝ) - 1 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hnx
      rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at h
    exact ⟨hn1, hnxR, small_factor_unit hp hn1
      (by exact_mod_cast (show (n : ℝ) < p by linarith))⟩
  · intro r hr
    have hprime := (primesUpTo_mem.mp hr).1
    have hbound := (atomIndex_bounds (primeCutoff ((p : ℝ) - 1)) (⟨r, hr⟩, false)).2
    change (r : ℝ) ≤ primeCutoff ((p : ℝ) - 1) ^ 2 at hbound
    exact small_factor_unit hp hprime.pos
      (by exact_mod_cast (show (r : ℝ) < p by linarith))
  · intro j hj
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact (le_mul_of_one_le_left (by positivity) hx).trans_lt (hsize j hj)

/-- Weighted smooth comparison on the full short interval, with all arithmetic
conditions derived and coefficient energy supplied by the actual norm bounds. -/
theorem eventual_weighted_smooth_comparison : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    let A := factorCount x
    let S := taylorOrder x
    ∀ [NeZero (p ^ 2)], p.Prime → ∀ delta : ℝ, 0 < delta → ∀ J : ℕ, 0 < J →
    ∀ (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo P → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo P → ‖c2 i r‖ ≤ 1) →
    |uniformAverage (fun χ : Character (p ^ 2) =>
        ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * χ (n : ZMod (p ^ 2))‖ ^ 2 *
          smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod (p ^ 2)))) -
      ∫ ω, ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * steinhaus n ω‖ ^ 2 *
        smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      2 * shortEnergy P (Finset.Icc 1 (p - 1)) w * errorSum delta J S A (2 * unitPrimeEnergy P) := by
  filter_upwards [eventual_comparison_data, eventual_short_prime_taylor_comparison] with p hd ht
  dsimp only at hd ht ⊢
  intro _ hp delta hdelta J hJ labels c1 c2 w h1 h2
  have hdata := hd hp
  have hB i : 2 * primeEnergy (primeCutoff ((p : ℝ) - 1)) (c1 i) (c2 i) ≤
      2 * unitPrimeEnergy (primeCutoff ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left (primeEnergy_le_unit _ _ _ (h1 i) (h2 i)) (by norm_num)
  have hc := character_weighted_approximation_bound hdelta hJ hdata.1 _ _ _ _ labels c1 c2 w
    hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hB
  have hr := random_weighted_approximation_bound hdelta hJ hdata.1 _ _ _ labels c1 c2 w
    (fun n hn => (hdata.2.1 n hn).1.ne') hB
  have h := abs_sub_le_of_middle_eq hc hr (by
    simpa only [mul_comm] using ht hp delta J labels c1 c2 w)
  simpa only [mul_assoc] using h

/-- The partition-weight comparison uses the sharper unweighted moment and
therefore omits the factor two inside the prime energy. -/
theorem eventual_smooth_weight_comparison : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    let A := factorCount x
    let S := taylorOrder x
    ∀ [NeZero (p ^ 2)], p.Prime → ∀ delta : ℝ, 0 < delta → ∀ J : ℕ, 0 < J →
    ∀ (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo P → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo P → ‖c2 i r‖ ≤ 1) →
    |uniformAverage (fun χ : Character (p ^ 2) =>
        smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod (p ^ 2)))) -
      ∫ ω, smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      2 * errorSum delta J S A (unitPrimeEnergy P) := by
  filter_upwards [eventual_comparison_data, eventual_prime_taylor_comparison] with p hd ht
  dsimp only at hd ht ⊢
  intro _ hp delta hdelta J hJ labels c1 c2 h1 h2
  have hdata := hd hp
  have hB i := primeEnergy_le_unit (primeCutoff ((p : ℝ) - 1)) (c1 i) (c2 i) (h1 i) (h2 i)
  have hc := character_approximation_bound hdelta hJ hdata.1 _ _ labels c1 c2
    hdata.2.2.1 hdata.2.2.2.2 hB
  have hr := random_approximation_bound hdelta hJ hdata.1 _ _ labels c1 c2 hB
  apply abs_sub_le_of_middle_eq hc hr
  have hs : ∀ n ∈ ({1} : Finset ℕ), 0 < n ∧ (n : ℝ) ≤ (p : ℝ) - 1 := by
    intro n hn
    have hn1 := Finset.mem_singleton.mp hn
    subst n
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact ⟨by norm_num, by norm_num; linarith⟩
  simpa using ht hp delta J labels c1 c2 {1} (fun _ => 1) hs

end NField.Alignment.HarperSmoothComparison
