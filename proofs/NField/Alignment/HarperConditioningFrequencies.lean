/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRetainedTransfer

/-!
# The actual conditioning frequencies in Harper's reduction

The finite factor index enumerates every integer -K through K exactly.
The first and second prime coefficients are the phases at t=k/ell^1.01
and 2t, with the literal factor one half on prime squares. Their norms
discharge the coefficient hypotheses of the proved transfer. The resulting
random conditioning sum is a concrete target, not an assumed estimate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperConditioningFrequencies

open scoped BigOperators
open Filter HarperRoundedCutoff HarperActualConditioning HarperRetainedTransfer
  HarperConditioningDecay CollisionCharacterStructure SpectralRepulsion

def frequencyIndex (x : ℝ) (i : Fin (factorCount x)) : ℤ :=
  (i.val : ℤ) - (frequencyRadius x : ℤ)

def frequency (x : ℝ) (i : Fin (factorCount x)) : ℝ :=
  (frequencyIndex x i : ℝ) / (cutoffLog x)^(101/100 : ℝ)

theorem frequencyIndex_bounds (x : ℝ) (i : Fin (factorCount x)) :
    -(frequencyRadius x : ℤ) ≤ frequencyIndex x i ∧
      frequencyIndex x i ≤ (frequencyRadius x : ℤ) := by
  have hi := i.isLt
  dsimp only [factorCount] at hi
  dsimp only [frequencyIndex]
  omega

theorem frequencyIndex_injective (x : ℝ) : Function.Injective (frequencyIndex x) := by
  intro i j h
  apply Fin.ext
  dsimp only [frequencyIndex] at h
  omega

theorem frequencyIndex_covers (x : ℝ) (k : ℤ)
    (hk0 : -(frequencyRadius x : ℤ) ≤ k) (hk1 : k ≤ (frequencyRadius x : ℤ)) :
    ∃ i : Fin (factorCount x), frequencyIndex x i = k := by
  have hi : (k + (frequencyRadius x : ℤ)).toNat < factorCount x := by
    dsimp only [factorCount]
    omega
  refine ⟨⟨(k + (frequencyRadius x : ℤ)).toNat, hi⟩, ?_⟩
  dsimp only [frequencyIndex]
  omega

def primePhase (t : ℝ) (r : ℕ) : ℂ :=
  Complex.exp (-((t * Real.log r : ℝ) : ℂ) * Complex.I)

theorem primePhase_norm (t : ℝ) (r : ℕ) : ‖primePhase t r‖ = 1 := by
  simp only [primePhase, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, neg_zero, Real.exp_zero]

theorem primePhase_eq_cpow {r : ℕ} (hr : 0 < r) (t : ℝ) :
    primePhase t r = (r : ℂ)^(-(t : ℂ) * Complex.I) := by
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hl : Complex.log (r : ℂ) = (Real.log (r : ℝ) : ℂ) :=
    (Complex.ofReal_log (Nat.cast_nonneg r)).symm
  rw [primePhase, Complex.cpow_def_of_ne_zero hn, hl]
  congr 1
  push_cast
  ring

theorem primePhase_div_rpow {r : ℕ} (hr : 0 < r) (t a : ℝ) :
    primePhase t r / (((r : ℝ)^a : ℝ) : ℂ) =
      (r : ℂ)^(-(a : ℂ) - (t : ℂ)*Complex.I) := by
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [primePhase_eq_cpow hr, Complex.ofReal_cpow (Nat.cast_nonneg r),
    show -(a : ℂ) - (t : ℂ)*Complex.I = -(t : ℂ)*Complex.I - (a : ℂ) by ring,
    Complex.cpow_sub _ _ hn]
  simp only [Complex.ofReal_natCast]

def firstCoefficient (x : ℝ) (i : Fin (factorCount x)) (r : ℕ) : ℂ :=
  primePhase (frequency x i) r

def secondCoefficient (x : ℝ) (i : Fin (factorCount x)) (r : ℕ) : ℂ :=
  (1/2 : ℂ) * primePhase (2 * frequency x i) r

theorem coefficient_norms (x : ℝ) (i : Fin (factorCount x)) (r : ℕ) :
    ‖firstCoefficient x i r‖ = 1 ∧ ‖secondCoefficient x i r‖ = (1/2 : ℝ) := by
  simp [firstCoefficient, secondCoefficient, primePhase_norm]

theorem coefficient_formulas (x : ℝ) (i : Fin (factorCount x)) {r : ℕ} (hr : 0 < r) :
    firstCoefficient x i r / (Real.sqrt (r : ℝ) : ℂ) =
      (r : ℂ)^(-(1/2 : ℂ) - (frequency x i : ℂ)*Complex.I) ∧
    secondCoefficient x i r / (r : ℂ) =
      (1/2 : ℂ) * (r : ℂ)^(-(1 : ℂ) - ((2*frequency x i : ℝ) : ℂ)*Complex.I) := by
  constructor
  · simpa only [firstCoefficient, Real.sqrt_eq_rpow, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using primePhase_div_rpow hr (frequency x i) (1/2)
  · have h := primePhase_div_rpow hr (2*frequency x i) 1
    simp only [Real.rpow_one, Complex.ofReal_natCast, Complex.ofReal_one] at h
    rw [secondCoefficient, mul_div_assoc, h]

def actualRandomConditioning (p : ℕ) : ℝ :=
  randomRetainedConditioning p (firstCoefficient ((p : ℝ)-1))
    (secondCoefficient ((p : ℝ)-1)) (fun _ => 1)

/-- All character-side and comparison errors are discharged. The bound
on this actual random conditioning sum remains the analytic proof target. -/
theorem eventual_actual_character_reduction {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero (p^2)], p.Prime →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      2 * actualRandomConditioning p + epsilon * targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_retained_transfer_negligible he] with p hp
  intro _ hprime
  have h := hp hprime (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
    (fun _ => 1)
    (fun i r _ => (coefficient_norms _ i r).1.le)
    (fun i r _ => by rw [(coefficient_norms _ i r).2]; norm_num)
    (fun n _ => by norm_num)
  simpa only [one_mul, actualRandomConditioning] using h

end NField.Alignment.HarperConditioningFrequencies
