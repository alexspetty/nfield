/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindCarrierFourierBound

/-!
# Finite Fourier completion with the zero frequency retained

An arbitrary residue function need not have zero mean. These bounds include
its zero Fourier mode, unlike the specialized Dedekind interval estimate.
-/

set_option autoImplicit false
namespace NField.Alignment.FiniteIntervalCompletion

open scoped BigOperators ZMod
open AddChar
open SpectralPower DedekindCarrierFourierBound DedekindFourierMoment

theorem interval_fourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (start length : ℕ) :
    (∑ a ∈ Finset.range length, f ((start + a : ℕ) : ZMod q)) =
      (q : ℂ)⁻¹ * ∑ t : ZMod q,
        ZMod.stdAddChar (t * (start : ZMod q)) *
          intervalFourier q length (-t) * ZMod.dft f t := by
  have hinv (x : ZMod q) : f x = (q : ℂ)⁻¹ * ∑ t : ZMod q,
      ZMod.stdAddChar (t * x) * ZMod.dft f t := by
    have h := congrFun (ZMod.dft.symm_apply_apply f) x
    rw [ZMod.invDFT_apply] at h
    simpa [smul_eq_mul] using h.symm
  simp_rw [hinv]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold intervalFourier
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.cast_add, mul_add, map_add_eq_mul]
  congr 2
  apply congrArg ZMod.stdAddChar
  ring

/-- Full L1 frequency bound, including the length contributed at zero. -/
theorem interval_fourier_norm_sum {q : ℕ} [NeZero q] (hq : 0 < q)
    (length : ℕ) :
    (∑ t : ZMod q, ‖intervalFourier q length t‖) ≤
      (length : ℝ) + (q : ℝ) * (harmonic q : ℝ) := by
  classical
  let w : ZMod q → ℝ := fun t => if t = 0 then 0 else
    1 / (DedekindFourierMoment.circularDistance q t.val : ℝ)
  have hterm (t : ZMod q) : ‖intervalFourier q length t‖ ≤
      (if t = 0 then (length : ℝ) else 0) + (q : ℝ) / 2 * w t := by
    by_cases ht : t = 0
    · subst t
      simp [intervalFourier, w]
    · simpa [w, ht, div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc,
        div_eq_mul_inv] using norm_intervalFourier_le_circular hq (length := length) ht
  calc
    _ ≤ ∑ t : ZMod q,
        ((if t = 0 then (length : ℝ) else 0) + (q : ℝ) / 2 * w t) :=
      Finset.sum_le_sum fun t _ => hterm t
    _ = (length : ℝ) + (q : ℝ) / 2 * ∑ t : ZMod q, w t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ (length : ℝ) + (q : ℝ) / 2 * (2 * (harmonic q : ℝ)) := by
      gcongr
      exact sum_nonzero_circular_reciprocal_le hq
    _ = _ := by ring

/-- Uniform complete-transform control implies interval control. The
`length/q` term is retained; no zero-mean premise is needed. -/
theorem interval_norm_le_of_dft {q : ℕ} [NeZero q] (hq : 0 < q)
    (f : ZMod q → ℂ) {U : ℝ} (hU : 0 ≤ U)
    (hbound : ∀ t : ZMod q, ‖ZMod.dft f t‖ ≤ U) (start length : ℕ) :
    ‖∑ a ∈ Finset.range length, f ((start + a : ℕ) : ZMod q)‖ ≤
      U * ((length : ℝ) / q + (harmonic q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hneg : (∑ t : ZMod q, ‖intervalFourier q length (-t)‖) =
      ∑ t : ZMod q, ‖intervalFourier q length t‖ := by
    simpa using Equiv.sum_comp (Equiv.neg (ZMod q))
      (fun t : ZMod q => ‖intervalFourier q length t‖)
  have hsum : ‖∑ t : ZMod q,
      ZMod.stdAddChar (t * (start : ZMod q)) *
        intervalFourier q length (-t) * ZMod.dft f t‖ ≤
      U * ((length : ℝ) + (q : ℝ) * (harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ t : ZMod q, ‖ZMod.stdAddChar (t * (start : ZMod q)) *
          intervalFourier q length (-t) * ZMod.dft f t‖ := norm_sum_le _ _
      _ ≤ ∑ t : ZMod q, U * ‖intervalFourier q length (-t)‖ := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul, norm_mul, AddChar.norm_apply, one_mul, mul_comm U]
        exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
      _ = U * ∑ t : ZMod q, ‖intervalFourier q length t‖ := by
        rw [← Finset.mul_sum, hneg]
      _ ≤ _ := mul_le_mul_of_nonneg_left (interval_fourier_norm_sum hq length) hU
  rw [interval_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * (U * ((length : ℝ) + (q : ℝ) * (harmonic q : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqR.le)
    _ = _ := by field_simp

end NField.Alignment.FiniteIntervalCompletion
