/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryWeightConstants
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # The zeta-derivative descriptions of the actual Möbius constants -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryZetaConstants
open scoped BigOperators LSeries.notation
open Filter StationaryWeightConstants MobiusReciprocalSquare

/-- Title: `The leading weight coefficient equals reciprocal zeta at two`. -/
theorem alpha_eq_reciprocal_zeta : (alpha : ℂ) = 1 / riemannZeta 2 := by
  rw [riemannZeta_two]
  unfold alpha
  push_cast
  ring

theorem mobius_series_eq_reciprocal_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / riemannZeta s := by
  have hp := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hp
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr (by simpa [mul_comm] using hp)

theorem mobius_series_eventually_eq_reciprocal_zeta :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) =ᶠ[nhds (2 : ℂ)]
      (fun s => 1 / riemannZeta s) := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨{z : ℂ | 1 < z.re}, ?_, fun _ h => mobius_series_eq_reciprocal_zeta h⟩
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

theorem mobius_log_term_complex (j n : ℕ) :
    (mobiusLogTerm j n : ℂ) =
      LSeries.term (LSeries.logMul^[j] (fun n => (ArithmeticFunction.moebius n : ℂ))) 2 n := by
  have he : (LSeries.logMul^[j] (fun n => (ArithmeticFunction.moebius n : ℂ))) n =
      Complex.log n ^ j * ArithmeticFunction.moebius n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih]
      ring
  by_cases hn : n = 0
  · subst n
    simp [mobiusLogTerm, mobiusReciprocalSquare, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, he]
    unfold mobiusLogTerm mobiusReciprocalSquare
    push_cast
    rw [Complex.cpow_two]
    ring

theorem mobius_log_moment_complex (j : ℕ) :
    (mobiusLogMoment j : ℂ) =
      LSeries (LSeries.logMul^[j] (fun n => (ArithmeticFunction.moebius n : ℂ))) 2 := by
  rw [mobiusLogMoment, Complex.ofReal_tsum]
  exact tsum_congr (mobius_log_term_complex j)

theorem mobius_abscissa_lt_two :
    LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.moebius n : ℂ)) < (2 : ℂ).re := by
  rw [ArithmeticFunction.abscissaOfAbsConv_moebius]
  change (1 : EReal) < ((2 : ℝ) : EReal)
  exact_mod_cast (by norm_num : (1 : ℝ) < 2)

/-- Title: `The first Möbius logarithmic moment is the zeta derivative ratio`. -/
theorem first_mobius_log_moment :
    (mobiusLogMoment 1 : ℂ) = deriv riemannZeta 2 / riemannZeta 2 ^ 2 := by
  have hd := (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).hasDerivAt
  have hi := hd.inv (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re))
  have he := mobius_series_eventually_eq_reciprocal_zeta.deriv_eq
  simp only [one_div] at he
  change _ = deriv (riemannZeta⁻¹) 2 at he
  rw [LSeries_deriv mobius_abscissa_lt_two, hi.deriv] at he
  have hm := mobius_log_moment_complex 1
  simp only [Function.iterate_one] at hm
  rw [← hm] at he
  linear_combination -he

/-- Title: `The second Möbius logarithmic moment is the second reciprocal-zeta derivative`. -/
theorem second_mobius_log_moment :
    (mobiusLogMoment 2 : ℂ) = iteratedDeriv 2 (fun s : ℂ => 1 / riemannZeta s) 2 := by
  have he := mobius_series_eventually_eq_reciprocal_zeta.iteratedDeriv_eq 2
  rw [LSeries_iteratedDeriv 2 mobius_abscissa_lt_two, ← mobius_log_moment_complex 2] at he
  norm_num at he
  simpa only [one_div] using he

end NField.Alignment.StationaryZetaConstants
