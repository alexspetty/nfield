/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTwistMass
import NField.Alignment.CommonResetCompletion
import NField.Alignment.CommonResetBernoulliLifts
import NField.Alignment.DivisorSmallPowerBound

/-! # The actual completed reciprocal phase with proved derivative input -/

noncomputable section

namespace NField.Alignment.CommonResetCompletedDerivative

open scoped BigOperators
open Set CommonResetDerivativeFirst CommonResetTwistDerivatives CommonResetTwistMass
open CommonResetCompletion CommonResetBernoulliLifts InverseAdditiveCompletion

theorem integer_character_phase {u : ℕ} [NeZero u] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod u) = phase ((z : ℝ)/u) := by
  rw [ZMod.stdAddChar_coe, phase_exp]
  congr 1
  push_cast
  ring

theorem integer_twist_sum {u : ℕ} [NeZero u] (h : ZMod u) (a : ℤ) (N : ℕ) (f : ℝ → ℝ) :
    (∑ i ∈ Finset.range (N+1), ZMod.stdAddChar (h*((a+(i : ℤ) : ℤ) : ZMod u))*
      phase (f ((a : ℝ)+i))) = linearTwistSum f a N u h.val := by
  unfold linearTwistSum
  apply Finset.sum_congr rfl
  intro i _
  have he : h*((a+(i : ℤ) : ℤ) : ZMod u) = (((h.val : ℤ)*(a+i) : ℤ) : ZMod u) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [he, integer_character_phase, ← phase_add]
  congr 1
  push_cast
  ring

def reciprocalInterval {u : ℕ} [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ) (f : ℝ → ℝ) : ℂ :=
  ∑ i ∈ Finset.range (N+1), inversePhase 1 n ((a+(i : ℤ) : ℤ) : ZMod u)*
    phase (f ((a : ℝ)+i))

def completedDerivativeScale (u N : ℕ) (lam : ℝ) : ℝ :=
  ((N : ℝ)+1)*Real.sqrt ((u : ℝ)*lam) + 1/Real.sqrt ((u : ℝ)*lam) +
    Real.sqrt (u : ℝ)*Real.log (2*(u : ℝ))

theorem completedDerivativeScale_nonneg {u : ℕ} (hu : 0 < u) (N : ℕ) (lam : ℝ) :
    0 ≤ completedDerivativeScale u N lam := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog : 0 ≤ Real.log (2*(u : ℝ)) := Real.log_nonneg (by linarith)
  unfold completedDerivativeScale
  positivity

/-- Title: `The completed reciprocal interval obeys the proved curvature bound at every modulus`. -/
theorem completed_reciprocal_interval_bound {u : ℕ} [NeZero u]
    (n : ZMod u) (a : ℤ) (N : ℕ) (f g k : ℝ → ℝ)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc (a : ℝ) (a+N)))
    (hfg : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc (a : ℝ) (a+N)))
    (hgk : ∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo (a : ℝ) (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    ‖reciprocalInterval n a N f‖ ≤ 160*(A+1)^2*(u.divisors.card : ℝ)*
      Real.sqrt (n.val.gcd u : ℝ)*completedDerivativeScale u N lam := by
  have hu : 0 < u := NeZero.pos u
  have hb := reciprocal_twist_mass_bound (Finset.range (N+1))
    (fun i : ℕ => ((a+(i : ℤ) : ℤ) : ZMod u)) (fun i : ℕ => phase (f ((a : ℝ)+i))) n
  simp only [integer_twist_sum] at hb
  rw [CommonResetBernoulliLifts.sum_residue_values (m := u)
    (fun h : ℕ => ‖linearTwistSum f a N u h‖)] at hb
  have ht := sum_linear_twists f g k a N hu hlam hA hf hfg hg hgk hk
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hsU : Real.sqrt (u : ℝ) ≠ 0 := (Real.sqrt_pos.mpr huR).ne'
  have hsL : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  calc
    _ ≤ (4*Real.sqrt (u : ℝ)*u.divisors.card*Real.sqrt (n.val.gcd u : ℝ))/(u : ℝ)*
        ∑ h ∈ Finset.range u, ‖linearTwistSum f a N u h‖ := hb
    _ ≤ (4*Real.sqrt (u : ℝ)*u.divisors.card*Real.sqrt (n.val.gcd u : ℝ))/(u : ℝ)*
        (40*(A+1)^2*((u : ℝ)*((N : ℝ)+1)*Real.sqrt lam + 1/Real.sqrt lam +
          (u : ℝ)*Real.log (2*(u : ℝ)))) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      unfold completedDerivativeScale
      rw [Real.sqrt_mul huR.le]
      have hsq := Real.sq_sqrt huR.le
      field_simp
      nlinarith

/-- Title: `The reciprocal-phase estimate has a constant uniform in every conductor and interval`. -/
theorem completed_reciprocal_small_power (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℕ) [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ)
      (f g k : ℝ → ℝ) (lam : ℝ), 0 < lam →
      ContinuousOn f (Icc (a : ℝ) (a+N)) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt f (g x) x) →
      ContinuousOn g (Icc (a : ℝ) (a+N)) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), HasDerivAt g (k x) x) →
      (∀ x ∈ Ioo (a : ℝ) (a+N), lam ≤ k x ∧ k x ≤ A*lam) →
      ‖reciprocalInterval n a N f‖ ≤ C*(u : ℝ)^ε*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N lam := by
  obtain ⟨D, hD, hbound⟩ := DivisorSmallPowerBound.divisor_count_small_power ε hε
  refine ⟨160*(A+1)^2*D, by positivity, ?_⟩
  intro u inst n a N f g k lam hlam hf hfg hg hgk hk
  have hb := completed_reciprocal_interval_bound n a N f g k hlam hA hf hfg hg hgk hk
  calc
    _ ≤ 160*(A+1)^2*(u.divisors.card : ℝ)*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N lam := hb
    _ ≤ 160*(A+1)^2*(D*(u : ℝ)^ε)*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N lam := by
      apply mul_le_mul_of_nonneg_right _ (completedDerivativeScale_nonneg (NeZero.pos u) N lam)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left (hbound u (NeZero.pos u)) (by positivity)
    _ = _ := by ring

end NField.Alignment.CommonResetCompletedDerivative
