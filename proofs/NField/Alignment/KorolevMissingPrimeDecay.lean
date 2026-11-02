/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevMissingPrimeCount

/-!
# Missing-prime counts at Korolev's exact smooth cutoff

Add back the proved smooth count, then specialize the general missing-prime
estimate at Q=exp(log x/log(log x)). The resulting bound is uniform in the
selected prime set and in a modulus used to restrict the counted integers.
The logarithmic-decay corollary retains its explicit reciprocal-mass
hypothesis; the source's chosen interval family has not been substituted.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevMissingPrimeDecay
open scoped BigOperators Topology Classical
open Filter CollisionMertensInput HarperSmoothCount HarperRoundedCutoff
  HarperSmoothCountDecay KorolevSmoothCount KorolevMissingPrimeCount

theorem avoid_count_split {x Q : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    ((avoidSet x S).card : ℝ) ≤ smoothCount x Q + ((nonsmoothAvoidSet x Q S).card : ℝ) := by
  have hs : avoidSet x S ⊆ smoothSet x Q ∪ nonsmoothAvoidSet x Q S := by
    intro n hn
    by_cases hsm : n ∈ HarperSmoothDivisor.smoothIntegers Q
    · obtain ⟨hn0, hnx, _⟩ := (avoidSet_mem hx S n).mp hn
      exact Finset.mem_union_left _ (smoothSet_mem.mpr ⟨hn0, hnx, hsm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, hsm⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  unfold smoothCount
  exact_mod_cast hc

theorem eventual_smoothCutoff_le : ∀ᶠ x : ℝ in atTop, smoothCutoff x ≤ x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hx hu
  dsimp only [Function.comp_apply] at hu
  unfold smoothCutoff
  conv_rhs => rw [← Real.rpow_one x]
  exact Real.rpow_le_rpow_of_exponent_le hx
    ((div_le_one (by linarith : 0 < Real.log (Real.log x))).mpr hu)

/-- Actual count of all positive integers up to x avoiding S. All prime
sets below the exact cutoff share one absolute constant and threshold. -/
theorem eventual_avoid_count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ S : Finset ℕ, S ⊆ primesUpTo (smoothCutoff x) →
      ((avoidSet x S).card : ℝ) ≤ C *
        (x / (Real.log x * Real.log (Real.log x)) + x * Real.log (Real.log x) *
          Real.exp (-(∑ p ∈ S, (1 : ℝ) / p))) := by
  obtain ⟨A, hA, hsmooth⟩ := eventual_smoothCount_two_bound
  obtain ⟨B, hB, hrough⟩ := eventual_nonsmooth_count_bound
  refine ⟨A+B, by positivity, ?_⟩
  filter_upwards [hsmooth, smoothCutoff_tendsto.eventually hrough, eventual_smoothCutoff_le,
    eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x hs hr hQx hx hu S hS
  dsimp only [Function.comp_apply] at hu
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hb := hr x hQx S hS
  have he : x * Real.log x / Real.log (smoothCutoff x) = x * Real.log (Real.log x) := by
    rw [log_smoothCutoff (by linarith)]
    field_simp
  rw [he] at hb
  have hc := avoid_count_split (Q := smoothCutoff x) hx0 S
  have ha0 : 0 ≤ x / (Real.log x * Real.log (Real.log x)) := by positivity
  have hb0 : 0 ≤ x * Real.log (Real.log x) * Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) := by positivity
  nlinarith

/-- Uniform coprime restriction, on the literal finite summation set. -/
theorem eventual_coprime_avoid_count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ S : Finset ℕ, S ⊆ primesUpTo (smoothCutoff x) → ∀ m : ℕ,
      (((avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤ C *
        (x / (Real.log x * Real.log (Real.log x)) + x * Real.log (Real.log x) *
          Real.exp (-(∑ p ∈ S, (1 : ℝ) / p))) := by
  obtain ⟨C, hC, h⟩ := eventual_avoid_count_bound
  refine ⟨C, hC, h.mono ?_⟩
  intro x hx S hS m
  have hc : (((avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤ ((avoidSet x S).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le (avoidSet x S) (fun n => n.Coprime m)
  exact hc.trans (hx S hS)

/-- A lower reciprocal-mass bound, with an explicit additive error, implies
logarithmic decay uniformly even when gamma and the prime set vary with x.
The mass condition remains explicit until the chosen source windows have
been proved to satisfy it. -/
theorem eventual_avoid_count_of_mass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ S : Finset ℕ, S ⊆ primesUpTo (smoothCutoff x) → ∀ gamma error : ℝ,
      gamma * Real.log (Real.log x) - error ≤ ∑ p ∈ S, (1 : ℝ) / p → ∀ m : ℕ,
        (((avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤ C *
          (x / (Real.log x * Real.log (Real.log x)) +
            x * Real.log (Real.log x) * (Real.exp error * (Real.log x)^(-gamma))) := by
  obtain ⟨C, hC, h⟩ := eventual_coprime_avoid_count_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hx hx1 hu S hS gamma error hmass m
  dsimp only [Function.comp_apply] at hu
  have he : Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) ≤ Real.exp error * (Real.log x)^(-gamma) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hx1), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (hx S hS m).trans
  have hweight : 0 ≤ x * Real.log (Real.log x) := mul_nonneg (by linarith) hu
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (x / (Real.log x * Real.log (Real.log x))))
      (mul_le_mul_of_nonneg_left he hweight)) hC.le

end NField.Alignment.KorolevMissingPrimeDecay
