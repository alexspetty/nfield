/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeManuscriptConsequences
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Vanishing errors in ordinary prime averages -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset Asymptotics
open scoped BigOperators Topology

theorem prime_indicator_sum (N : ℕ) :
    (∑ n ∈ range N, if n.Prime then (1 : ℝ) else 0) =
      (Nat.primeCounting' N : ℝ) := by
  classical
  simp only [Nat.primeCounting', Nat.count_eq_card_filter_range,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem real_sum_Ioc_eq_range_succ {f : ℕ → ℝ} (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, f n) = ∑ n ∈ Finset.range (N + 1), f n := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Ioc, Finset.mem_range] at hn hnot
      omega
    simpa [hn0] using hf

/-- Title: `A vanishing error has vanishing ordinary prime average`.
Mathlib's weighted partial-sum little-o theorem supplies the Cesaro step. -/
theorem vanishing_prime_average {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => realPrimeTailSum e 0 x / (Nat.primeCounting ⌊x⌋₊ : ℝ))
      atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun n => if n.Prime then e n else 0
  let g : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  have hsmall : f =o[atTop] g := by
    apply isLittleO_iff.mpr
    intro ε hε
    filter_upwards [((isLittleO_one_iff ℝ).mpr he).bound hε] with n hn
    by_cases hp : n.Prime
    · simpa [f, g, hp] using hn
    · simp [f, g, hp]
  have hg : ∀ n, 0 ≤ g n := by intro n; dsimp [g]; split_ifs <;> positivity
  have hsum : Tendsto (fun N => ∑ n ∈ range N, g n) atTop atTop := by
    simpa only [g, prime_indicator_sum, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp Nat.tendsto_primeCounting'
  have h := (hsmall.sum_range hg hsum).tendsto_div_nhds_zero
  have hcut := h.comp (show Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop from
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
  apply hcut.congr'
  apply Filter.Eventually.of_forall
  intro x
  simp only [Function.comp_apply, g, prime_indicator_sum]
  rw [← real_sum_Ioc_eq_range_succ (f := f) (by simp [f, Nat.not_prime_zero])]
  rfl

theorem real_sum_Ioc_cutoff_eventually (f : ℕ → ℝ) (c : ℕ) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc c ⌊x⌋₊, f n) =ᶠ[atTop]
      (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) - ∑ n ∈ Finset.Ioc 0 c, f n) := by
  filter_upwards [tendsto_nat_floor_atTop.eventually (eventually_ge_atTop c)] with x hx
  have h := Finset.sum_Ioc_consecutive f (Nat.zero_le c) hx
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem vanishing_prime_tail_average {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (c : ℕ) :
    Tendsto (fun x : ℝ => realPrimeTailSum e c x / (Nat.primeCounting ⌊x⌋₊ : ℝ))
      atTop (𝓝 0) := by
  have hpi : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop)
  have hc := (tendsto_const_nhds.div_atTop hpi : Tendsto
    (fun x : ℝ => realPrimeTailSum e 0 c / (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 0))
  have h := (vanishing_prime_average he).sub hc
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [real_sum_Ioc_cutoff_eventually (fun n => if n.Prime then e n else 0) c] with x hx
  simp only [realPrimeTailSum, Nat.floor_natCast]
  rw [hx, sub_div]

/-- Title: `The unweighted constructive correction remainder tends to zero`. -/
theorem unweighted_correction_tendsto_zero {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ => (n : ℝ) * correctionTail b n) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) * correctionTail b n‖ ≤ (2 * (b : ℝ)) / n := by
    filter_upwards [eventually_ge_atTop (2 * (b + 1))] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    calc
      _ = (n : ℝ) * ‖correctionTail b n‖ := by rw [norm_mul, Real.norm_of_nonneg hn0.le]
      _ ≤ (n : ℝ) * ((2 * (b : ℝ)) * (1 / (n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left (correctionTail_norm_bound hb hn) hn0.le
      _ = (2 * (b : ℝ)) / n := by field_simp
  exact squeeze_zero_norm' hbound
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem filtered_vanishing_prime_tail_average {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (P : ℕ → Prop) [DecidablePred P] (c : ℕ) :
    Tendsto (fun x : ℝ => realPrimeTailSum (fun p => if P p then e p else 0) c x /
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 0) := by
  apply vanishing_prime_tail_average
  apply squeeze_zero_norm (a := fun n => ‖e n‖) _ (by simpa using he.norm)
  intro n
  split_ifs <;> simp

end NField.Alignment.CollisionPrimeLimits
