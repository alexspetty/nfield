/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue

/-! # The summation-by-parts kernel for ordinary Dirichlet convergence

The difference of two consecutive complex powers has a summable bound
on every bounded part of a closed right half-plane. No absolute
summability of the original coefficients is assumed.
-/
noncomputable section
set_option autoImplicit false

namespace NField.Alignment.OrdinaryDirichletKernel
open scoped Topology BigOperators
open Filter Set

def weight (n : ℕ) (s : ℂ) : ℂ := ((n+1 : ℕ) : ℂ) ^ (-s)

def difference (n : ℕ) (s : ℂ) : ℂ := weight n s - weight (n+1) s

theorem weight_differentiable (n : ℕ) : Differentiable ℂ (weight n) := by
  exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast Nat.succ_ne_zero n))

theorem difference_differentiable (n : ℕ) : Differentiable ℂ (difference n) :=
  (weight_differentiable n).sub (weight_differentiable (n+1))

theorem norm_weight (n : ℕ) (s : ℂ) :
    ‖weight n s‖ = ((n+1 : ℕ) : ℝ) ^ (-s.re) := by
  simpa [weight] using Complex.norm_cpow_eq_rpow_re_of_pos
    (by positivity : 0 < ((n+1 : ℕ) : ℝ)) (-s)

/-- Title: `Consecutive complex powers have a summable difference bound`. -/
theorem norm_difference_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖difference n s‖ ≤ ‖s‖ * ((n+1 : ℕ) : ℝ) ^ (-s.re-1) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)
  have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := ((n+1 : ℕ) : ℝ)) (b := ((n+2 : ℕ) : ℝ))
    (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s-1))
    (C := ‖s‖ * ((n+1 : ℕ) : ℝ) ^ (-s.re-1))
    (fun x hx => (hasDerivAt_ofReal_cpow_const (hn.trans_le hx.1).ne' hs0).hasDerivWithinAt)
    (by
      intro x hx
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hn.trans_le hx.1)]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hn hx.1 (by linarith)) (norm_nonneg s))
    ((n+2 : ℕ) : ℝ) (by constructor <;> norm_num)
  have hstep : ((n+2 : ℕ) : ℝ) - ((n+1 : ℕ) : ℝ) = 1 := by push_cast; ring
  rw [hstep, mul_one] at h
  simpa [difference, weight, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, norm_sub_rev, add_assoc] using h

theorem norm_difference_le_strip (n : ℕ) {δ R : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖difference n s‖ ≤ R * ((n+1 : ℕ) : ℝ) ^ (-δ-1) := by
  refine (norm_difference_le n (hδ.trans_le hs)).trans ?_
  exact mul_le_mul hR
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      (by linarith)) (Real.rpow_nonneg (by positivity) _) ((norm_nonneg s).trans hR)

theorem difference_majorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ) ^ (-δ-1)) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))

def partialSum (b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range n, b k

def abelTerm (b : ℕ → ℂ) (n : ℕ) (s : ℂ) : ℂ := difference n s * partialSum b (n+1)

def abelSum (b : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ, abelTerm b n s

/-- The finite identity retains its exact final boundary term. -/
theorem finite_identity (b : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), weight k s * b k) =
      weight n s * partialSum b (n+1) + ∑ k ∈ Finset.range n, abelTerm b k s := by
  have h := Finset.sum_range_by_parts (fun k => weight k s) b (n+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  simp only [partialSum, abelTerm, difference, sub_mul, Finset.sum_sub_distrib]
  ring

theorem norm_abelTerm_le {b : ℕ → ℂ} {B δ R : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) (hδ : 0 < δ) (n : ℕ) {s : ℂ}
    (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖abelTerm b n s‖ ≤ (R * B) * ((n+1 : ℕ) : ℝ) ^ (-δ-1) := by
  rw [abelTerm, norm_mul]
  calc
    _ ≤ (R * ((n+1 : ℕ) : ℝ) ^ (-δ-1)) * B :=
      mul_le_mul (norm_difference_le_strip n hδ hs hR) (hb (n+1))
        (norm_nonneg _) ((norm_nonneg _).trans (norm_difference_le_strip n hδ hs hR))
    _ = _ := by ring

theorem abelTerm_summable {b : ℕ → ℂ} {B : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => abelTerm b n s) := by
  apply Summable.of_norm_bounded
    ((difference_majorant_summable hs).mul_left (‖s‖ * B))
  intro n
  exact norm_abelTerm_le hb hs n le_rfl le_rfl

theorem abelSum_differentiableOn {b : ℕ → ℂ} {B δ R : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) (hδ : 0 < δ) :
    DifferentiableOn ℂ (abelSum b) {s : ℂ | δ < s.re ∧ ‖s‖ < R} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((difference_majorant_summable hδ).mul_left (R * B))
  · intro n
    exact ((difference_differentiable n).mul_const (partialSum b (n+1))).differentiableOn
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  · intro n s hs
    exact norm_abelTerm_le hb hδ n hs.1.le hs.2.le

/-- Title: `Bounded partial sums give an analytic Dirichlet sum on the right half-plane`. -/
theorem abelSum_analyticOnNhd {b : ℕ → ℂ} {B : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) :
    AnalyticOnNhd ℂ (abelSum b) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hδ : 0 < s.re / 2 := by change 0 < s.re at hs; linarith
  exact (abelSum_differentiableOn (R := ‖s‖+1) hb hδ).analyticOnNhd
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)) s ⟨by linarith, by linarith⟩

theorem weight_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => weight n s) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [norm_weight]
  exact (tendsto_rpow_neg_atTop hs).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Title: `The analytic Abel sum is the ordinary ordered Dirichlet limit`. -/
theorem ordinary_convergence {b : ℕ → ℂ} {B : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, weight k s * b k) atTop (𝓝 (abelSum b s)) := by
  have hboundary : Tendsto (fun n => weight n s * partialSum b (n+1)) atTop (𝓝 0) := by
    exact NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      (weight_tendsto_zero hs)
      ⟨B, eventually_map.mpr (Eventually.of_forall (fun n => hb (n+1)))⟩
  have hsum := (abelTerm_summable hb hs).hasSum.tendsto_sum_nat
  have h := hboundary.add hsum
  rw [zero_add] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact h.congr (fun n => (finite_identity b s n).symm)

/-- Title: `Ordinary Dirichlet partial sums converge uniformly on smaller bounded strips`. -/
theorem ordinary_uniform_convergence {b : ℕ → ℂ} {B δ R : ℝ}
    (hb : ∀ n, ‖partialSum b n‖ ≤ B) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun n s => ∑ k ∈ Finset.range n, weight k s * b k)
      (abelSum b) atTop {s : ℂ | δ ≤ s.re ∧ ‖s‖ ≤ R} := by
  have hB : 0 ≤ B := (norm_nonneg (partialSum b 0)).trans (hb 0)
  have hboundary : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ) ^ (-δ) * B) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).mul_const B
  have hsum := tendstoUniformlyOn_tsum_nat
    ((difference_majorant_summable hδ).mul_left (R * B))
    (fun n (s : ℂ) (hs : δ ≤ s.re ∧ ‖s‖ ≤ R) => norm_abelTerm_le hb hδ n hs.1 hs.2)
  rw [Metric.tendstoUniformlyOn_iff] at hsum ⊢
  intro ε hε
  have hhalf : 0 < ε/2 := by linarith
  have hshift : ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, δ ≤ s.re ∧ ‖s‖ ≤ R →
      dist (abelSum b s) (∑ k ∈ Finset.range (n+1), weight k s * b k) < ε := by
    filter_upwards [hboundary.eventually (gt_mem_nhds hhalf), hsum (ε/2) hhalf] with n hn hsum
    intro s hs
    have hbnd : ‖weight n s * partialSum b (n+1)‖ ≤ ((n+1 : ℕ) : ℝ) ^ (-δ) * B := by
      rw [norm_mul, norm_weight]
      exact mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
          (neg_le_neg hs.1)) (hb (n+1)) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    rw [finite_identity, dist_comm, dist_eq_norm]
    have heq : weight n s * partialSum b (n+1) + (∑ k ∈ Finset.range n, abelTerm b k s) - abelSum b s =
        weight n s * partialSum b (n+1) + ((∑ k ∈ Finset.range n, abelTerm b k s) - abelSum b s) := by ring
    rw [heq]
    have hsum' : ‖(∑ k ∈ Finset.range n, abelTerm b k s) - abelSum b s‖ < ε/2 := by
      simpa only [dist_eq_norm, norm_sub_rev, abelSum] using hsum s hs
    exact (norm_add_le _ _).trans_lt (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hshift
  apply eventually_atTop.mpr
  refine ⟨N+1, ?_⟩
  intro n hn s hs
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hN (n-1) (by omega) s hs

end NField.Alignment.OrdinaryDirichletKernel
