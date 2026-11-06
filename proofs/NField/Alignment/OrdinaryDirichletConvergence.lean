/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OrdinaryDirichletKernel

/-! # Holomorphy from ordinary Dirichlet convergence at one point

The coefficients are arbitrary complex numbers. Convergence is the limit
of the ordered partial sums, not unconditional `Summable` of the original
series. Mathlib's finite summation by parts and uniform analytic sum
criterion supply the analytic function in the open half-plane to the right.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.OrdinaryDirichletConvergence
open scoped Topology BigOperators
open Filter Set OrdinaryDirichletKernel

def term (a : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ := a n * weight n s

def sums (a : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, term a s n

theorem term_eq_div (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term a s n = a n / ((n+1 : ℕ) : ℂ) ^ s := by
  simp [term, weight, Complex.cpow_neg, div_eq_mul_inv]

theorem weight_shift (n : ℕ) (s t : ℂ) : weight n (s-t) * weight n t = weight n s := by
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [weight, weight, weight, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

theorem term_shift (a : ℕ → ℂ) (s t : ℂ) (n : ℕ) :
    weight n (s-t) * term a t n = term a s n := by
  rw [term, term, mul_left_comm, weight_shift]

/-- Title: `One ordinary convergence point gives bounded weighted partial sums`. -/
theorem bounded_partial_sums {a : ℕ → ℂ} {s l : ℂ}
    (h : Tendsto (sums a s) atTop (𝓝 l)) :
    ∃ B : ℝ, ∀ n, ‖partialSum (term a s) n‖ ≤ B := by
  obtain ⟨B, hB⟩ := h.norm.bddAbove_range
  exact ⟨B, fun n => hB (Set.mem_range_self n)⟩

/-- Title: `Ordinary convergence gives a holomorphic sum throughout the right half-plane`. -/
theorem holomorphic_of_ordinary_convergence {a : ℕ → ℂ} {σ : ℝ} {l : ℂ}
    (h : Tendsto (sums a (σ : ℂ)) atTop (𝓝 l)) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s : ℂ | σ < s.re} ∧
      (∀ s : ℂ, σ < s.re → Tendsto (sums a s) atTop (𝓝 (F s))) ∧
      (∀ δ R : ℝ, 0 < δ → TendstoUniformlyOn (fun N s => sums a s N) F atTop
        {s : ℂ | δ ≤ (s-(σ : ℂ)).re ∧ ‖s-(σ : ℂ)‖ ≤ R}) := by
  obtain ⟨B, hb⟩ := bounded_partial_sums h
  let F : ℂ → ℂ := fun s => abelSum (term a (σ : ℂ)) (s-(σ : ℂ))
  refine ⟨F, ?_, ?_, ?_⟩
  · intro s hs
    change σ < s.re at hs
    have hpos : 0 < (s-(σ : ℂ)).re := by simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hs
    exact ((abelSum_analyticOnNhd hb) (s-(σ : ℂ)) hpos).comp
      (f := fun z : ℂ => z-(σ : ℂ)) (x := s) (analyticAt_id.sub analyticAt_const)
  · intro s hs
    have hpos : 0 < (s-(σ : ℂ)).re := by simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hs
    have ht := ordinary_convergence hb hpos
    change Tendsto (fun N => ∑ n ∈ Finset.range N, term a s n) atTop
      (𝓝 (abelSum (term a (σ : ℂ)) (s-(σ : ℂ))))
    simpa only [term_shift] using ht
  · intro δ R hδ
    have ht := (ordinary_uniform_convergence (R := R) hb hδ).comp (fun s : ℂ => s-(σ : ℂ))
    simpa [sums, term_shift, F, Function.comp_def] using ht

end NField.Alignment.OrdinaryDirichletConvergence
