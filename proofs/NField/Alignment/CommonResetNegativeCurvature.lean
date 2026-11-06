/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCompletedDerivative

/-! # Negative curvature by exact conjugation and reindexing every Fourier mode -/

noncomputable section

namespace NField.Alignment.CommonResetNegativeCurvature

open scoped BigOperators ComplexConjugate
open Set CommonResetDerivativeFirst CommonResetTwistDerivatives CommonResetTwistMass
open CommonResetCompletedDerivative CommonResetBernoulliLifts InverseAdditiveCompletion

theorem character_neg_conj {u : ℕ} [NeZero u] (x : ZMod u) :
    ZMod.stdAddChar (-x) = conj (ZMod.stdAddChar x) := by
  change ((ZMod.toCircle (-x) : Circle) : ℂ) = conj ((ZMod.toCircle x : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj _

/-- Title: `Conjugation reindexes the entire family of integer-interval Fourier twists`. -/
theorem twist_mass_neg_eq {u : ℕ} [NeZero u] (a : ℤ) (N : ℕ) (f : ℝ → ℝ) :
    (∑ h ∈ Finset.range u, ‖linearTwistSum (fun x => -f x) a N u h‖) =
      ∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖ := by
  rw [← sum_residue_values (m := u) (fun h : ℕ => ‖linearTwistSum (fun x => -f x) a N u h‖),
    ← sum_residue_values (m := u) (fun h : ℕ => ‖linearTwistSum f a N u h‖)]
  have he (h : ZMod u) : linearTwistSum (fun x => -f x) a N u (-h).val =
      conj (linearTwistSum f a N u h.val) := by
    rw [← integer_twist_sum, ← integer_twist_sum]
    simp only [map_sum, map_mul, phase_neg, neg_mul, character_neg_conj]
  calc
    _ = ∑ h : ZMod u, ‖linearTwistSum (fun x => -f x) a N u (-h).val‖ :=
      (Equiv.sum_comp (Equiv.neg (ZMod u))
        (fun h : ZMod u => ‖linearTwistSum (fun x => -f x) a N u h.val‖)).symm
    _ = _ := by simp only [he, Complex.norm_conj]

/-- Title: `The full linear-twist estimate also holds for negative second derivatives`. -/
theorem sum_linear_twists_negative (f g k : ℝ → ℝ) (a : ℤ) (N : ℕ)
    {u : ℕ} (hu : 0 < u) {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc (a : ℝ) (a+N)))
    (hfg : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc (a : ℝ) (a+N)))
    (hgk : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo (a : ℝ) (a+N), -A*lam ≤ k x ∧ k x ≤ -lam) :
    (∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖) ≤
      40*(A+1)^2*((u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 1/Real.sqrt lam +
        (u : ℝ)*Real.log (2*(u : ℝ))) := by
  letI : NeZero u := ⟨hu.ne'⟩
  rw [← twist_mass_neg_eq a N f]
  apply sum_linear_twists (fun x => -f x) (fun x => -g x) (fun x => -k x) a N hu hlam hA
    hf.neg (fun x hx => (hfg x hx).neg) hg.neg (fun x hx => (hgk x hx).neg)
  intro x hx
  have hh := hk x hx
  constructor <;> linarith [hh.1, hh.2]

theorem inversePhase_neg_conj {u : ℕ} [NeZero u] (n x : ZMod u) :
    inversePhase 1 (-n) x = conj (inversePhase 1 n x) := by
  unfold inversePhase
  split_ifs
  · simp only [neg_mul, character_neg_conj]
  · simp only [map_zero]

theorem reciprocalInterval_neg_conj {u : ℕ} [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ)
    (f : ℝ → ℝ) : reciprocalInterval (-n) a N (fun x => -f x) = conj (reciprocalInterval n a N f) := by
  simp only [reciprocalInterval, inversePhase_neg_conj, phase_neg, map_sum, map_mul]

theorem gcd_neg_val {u : ℕ} [NeZero u] (n : ZMod u) : (-n).val.gcd u = n.val.gcd u := by
  have h := PrimePowerGcdBound.gcd_val_mul_unit u n (-1) (isUnit_one.neg)
  simpa only [mul_neg, mul_one] using h

/-- Title: `Reduction of a signed integer frequency preserves its conductor gcd`. -/
theorem integer_frequency_gcd {u : ℕ} [NeZero u] (n : ℤ) :
    (n : ZMod u).val.gcd u = n.natAbs.gcd u := by
  change Int.gcd ((n : ZMod u).val : ℤ) (u : ℤ) = Int.gcd n (u : ℤ)
  rw [ZMod.val_intCast, Int.gcd_emod]

/-- Title: `The completed reciprocal estimate keeps negative curvature and the same frequency gcd`. -/
theorem completed_reciprocal_negative_bound {u : ℕ} [NeZero u]
    (n : ZMod u) (a : ℤ) (N : ℕ) (f g k : ℝ → ℝ)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc (a : ℝ) (a+N)))
    (hfg : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc (a : ℝ) (a+N)))
    (hgk : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo (a : ℝ) (a+N), -A*lam ≤ k x ∧ k x ≤ -lam) :
    ‖reciprocalInterval n a N f‖ ≤ 160*(A+1)^2*(u.divisors.card : ℝ)*
      Real.sqrt (n.val.gcd u : ℝ)*completedDerivativeScale u N lam := by
  have hneg : ∀ x ∈ Ioo (a : ℝ) (a+N), lam ≤ -k x ∧ -k x ≤ A*lam := by
    intro x hx
    have hh := hk x hx
    constructor <;> linarith [hh.1, hh.2]
  have hb := completed_reciprocal_interval_bound (-n) a N
    (fun x => -f x) (fun x => -g x) (fun x => -k x) hlam hA hf.neg
    (fun x hx => (hfg x hx).neg) hg.neg (fun x hx => (hgk x hx).neg) hneg
  rw [reciprocalInterval_neg_conj, Complex.norm_conj, gcd_neg_val] at hb
  exact hb

/-- Title: `The uniform small-power completion estimate includes negative curvature`. -/
theorem completed_reciprocal_negative_small_power (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℕ) [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ)
      (f g k : ℝ → ℝ) (lam : ℝ), 0 < lam →
      ContinuousOn f (Icc (a : ℝ) (a+N)) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt f (g x) x) →
      ContinuousOn g (Icc (a : ℝ) (a+N)) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt g (k x) x) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), -A*lam ≤ k x ∧ k x ≤ -lam) →
      ‖reciprocalInterval n a N f‖ ≤ C*(u : ℝ)^ε*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N lam := by
  obtain ⟨C, hC, hbound⟩ := completed_reciprocal_small_power A ε hA hε
  refine ⟨C, hC, ?_⟩
  intro u inst n a N f g k lam hlam hf hfg hg hgk hk
  have hneg : ∀ x ∈ Ioo (a : ℝ) (a+N), lam ≤ -k x ∧ -k x ≤ A*lam := by
    intro x hx
    have hh := hk x hx
    constructor <;> linarith [hh.1, hh.2]
  have hb := hbound u (-n) a N (fun x => -f x) (fun x => -g x) (fun x => -k x)
    lam hlam hf.neg (fun x hx => (hfg x hx).neg) hg.neg
    (fun x hx => (hgk x hx).neg) hneg
  rw [reciprocalInterval_neg_conj, Complex.norm_conj, gcd_neg_val] at hb
  exact hb

end NField.Alignment.CommonResetNegativeCurvature
