/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperDiscretizationScales
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The actual Euler-product logarithm and conditioning prime sum

A cubic local logarithmic remainder has a summable uniform majorant over
all primes. Real logarithms of the positive factor norms give an absolute
bound between log(norm(F_P)) and the actual prime-plus-prime-square sum,
without assuming additivity of the complex logarithm across branches.
Nonvanishing, exact coefficient correspondence and two-sided exponential
bounds are proved for the actual Steinhaus model and frequencies.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperEulerLogComparison
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperSmoothDivisor HarperSmoothCount HarperEulerSecondMoment HarperConditioningFrequencies
  HarperRoundedCutoff HarperPrimeTaylorComparison CollisionMertensInput

def primeTerm (q : ℕ) (t : ℝ) (ω : PhaseSpace) : ℂ :=
  steinhaus q ω/(q : ℂ)^(linePoint (1/2) t)
def quadraticPrimeSum (P t : ℝ) (ω : PhaseSpace) : ℝ :=
  (∑ q ∈ primesUpTo P, (primeTerm q t ω+(primeTerm q t ω)^2/2)).re
def logRemainderConstant : ℝ := 2*∑' n : ℕ, (n : ℝ)^(-(3/2 : ℝ))

theorem primeTerm_norm {q : ℕ} (hq : q ≠ 0) (t : ℝ) (ω : PhaseSpace) :
    ‖primeTerm q t ω‖ = (q : ℝ)^(-(1/2 : ℝ)) := by
  simpa only [primeTerm, termHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Complex.cpow_neg, ← div_eq_mul_inv, linePoint_re] using
    termHom_norm hq (linePoint (1/2) t) ω

theorem primeTerm_norm_le {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    ‖primeTerm q t ω‖ ≤ 3/4 := by
  rw [primeTerm_norm hq.ne_zero]
  exact HarperShiftedEulerProduct.prime_power_bound (by exact_mod_cast hq.two_le) le_rfl

theorem localFactor_ne_zero {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    1-primeTerm q t ω ≠ 0 := by
  intro he
  have hz : primeTerm q t ω = 1 := (sub_eq_zero.mp he).symm
  have h := primeTerm_norm_le hq t ω
  rw [hz, norm_one] at h
  norm_num at h

theorem eulerProduct_critical_ne_zero (P t : ℝ) (ω : PhaseSpace) :
    eulerProduct P (linePoint (1/2) t) ω ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact inv_ne_zero (localFactor_ne_zero (primesUpTo_mem.mp hq).1 t ω)

theorem local_log_quadratic_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    ‖Complex.log (1-z)⁻¹-(z+z^2/2)‖ ≤ 2*‖z‖^3 := by
  have h := Complex.norm_log_one_sub_inv_add_logTaylor_neg_le 2 (show ‖z‖ < 1 by linarith)
  have he : Complex.logTaylor (2+1) (-z) = -(z+z^2/2) := by
    norm_num [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  rw [he] at h
  have hi : (1-‖z‖)⁻¹ ≤ 4 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1-‖z‖)]
    linarith
  calc
    _ ≤ ‖z‖^(2+1)*(1-‖z‖)⁻¹/(2+1) := by simpa only [Nat.cast_ofNat, sub_eq_add_neg] using h
    _ ≤ ‖z‖^3*4/3 := by gcongr; norm_num
    _ ≤ _ := by nlinarith [pow_nonneg (norm_nonneg z) 3]

theorem prime_log_error_bound {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    |Real.log ‖(1-primeTerm q t ω)⁻¹‖-(primeTerm q t ω+(primeTerm q t ω)^2/2).re| ≤
      2*(q : ℝ)^(-(3/2 : ℝ)) := by
  have h := (Complex.abs_re_le_norm
    (Complex.log (1-primeTerm q t ω)⁻¹-(primeTerm q t ω+(primeTerm q t ω)^2/2))).trans
    (local_log_quadratic_bound (primeTerm_norm_le hq t ω))
  simp only [Complex.sub_re, Complex.log_re] at h
  rw [primeTerm_norm hq.ne_zero, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)] at h
  norm_num at h
  simpa using h

theorem log_eulerProduct_eq_sum (P t : ℝ) (ω : PhaseSpace) :
    Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖ =
      ∑ q ∈ primesUpTo P, Real.log ‖(1-primeTerm q t ω)⁻¹‖ := by
  change Real.log ‖∏ q ∈ primesUpTo P, (1-primeTerm q t ω)⁻¹‖ = _
  rw [norm_prod, Real.log_prod (fun q hq => norm_ne_zero_iff.mpr
    (inv_ne_zero (localFactor_ne_zero (primesUpTo_mem.mp hq).1 t ω)))]

theorem logRemainderConstant_nonneg : 0 ≤ logRemainderConstant :=
  mul_nonneg (by norm_num) (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

theorem log_eulerProduct_quadratic_bound (P t : ℝ) (ω : PhaseSpace) :
    |Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖-quadraticPrimeSum P t ω| ≤
      logRemainderConstant := by
  rw [log_eulerProduct_eq_sum]
  unfold quadraticPrimeSum
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ primesUpTo P,
        |Real.log ‖(1-primeTerm q t ω)⁻¹‖-(primeTerm q t ω+(primeTerm q t ω)^2/2).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ primesUpTo P, 2*(q : ℝ)^(-(3/2 : ℝ)) :=
      Finset.sum_le_sum (fun q hq => prime_log_error_bound (primesUpTo_mem.mp hq).1 t ω)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1)).sum_le_tsum _
        (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem primeTerm_eq_firstCoefficient (x : ℝ) (i : Fin (factorCount x))
    {q : ℕ} (hq : 0 < q) (ω : PhaseSpace) :
    primeTerm q (frequency x i) ω =
      firstCoefficient x i q*steinhaus q ω/(Real.sqrt q : ℂ) := by
  have h := (coefficient_formulas x i hq).1
  have he : -(1/2 : ℂ)-(frequency x i : ℂ)*Complex.I = -linePoint (1/2) (frequency x i) := by
    unfold linePoint
    push_cast
    ring
  rw [he, Complex.cpow_neg] at h
  unfold primeTerm
  rw [mul_div_right_comm, h]
  ring

theorem primeTerm_sq_eq_secondCoefficient (x : ℝ) (i : Fin (factorCount x))
    {q : ℕ} (hq : 0 < q) (ω : PhaseSpace) :
    (primeTerm q (frequency x i) ω)^2/2 =
      secondCoefficient x i q*steinhaus (q^2) ω/(q : ℂ) := by
  have h := (coefficient_formulas x i hq).2
  have he : -(1 : ℂ)-((2*frequency x i : ℝ) : ℂ)*Complex.I =
      (2 : ℕ)*(-linePoint (1/2) (frequency x i)) := by
    unfold linePoint
    push_cast
    ring
  rw [he, Complex.cpow_nat_mul, Complex.cpow_neg] at h
  rw [mul_div_right_comm, h, steinhaus_pow]
  unfold primeTerm
  ring

theorem quadraticPrimeSum_eq_primeArgument (P x : ℝ) (i : Fin (factorCount x)) (ω : PhaseSpace) :
    quadraticPrimeSum P (frequency x i) ω =
      primeArgument P (firstCoefficient x i) (secondCoefficient x i) (fun n => steinhaus n ω) := by
  unfold quadraticPrimeSum primeArgument
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [primeTerm_sq_eq_secondCoefficient x i (primesUpTo_mem.mp hq).1.pos,
    primeTerm_eq_firstCoefficient x i (primesUpTo_mem.mp hq).1.pos]

theorem actual_log_eulerProduct_primeArgument_bound (x : ℝ) (i : Fin (factorCount x)) (ω : PhaseSpace) :
    |Real.log ‖eulerProduct (primeCutoff x) (linePoint (1/2) (frequency x i)) ω‖-
      primeArgument (primeCutoff x) (firstCoefficient x i) (secondCoefficient x i)
        (fun n => steinhaus n ω)| ≤ logRemainderConstant := by
  simpa only [quadraticPrimeSum_eq_primeArgument] using
    log_eulerProduct_quadratic_bound (primeCutoff x) (frequency x i) ω


theorem eulerProduct_exp_bounds (P t : ℝ) (ω : PhaseSpace) :
    Real.exp (quadraticPrimeSum P t ω-logRemainderConstant) ≤
      ‖eulerProduct P (linePoint (1/2) t) ω‖ ∧
    ‖eulerProduct P (linePoint (1/2) t) ω‖ ≤
      Real.exp (quadraticPrimeSum P t ω+logRemainderConstant) := by
  have hn := norm_pos_iff.mpr (eulerProduct_critical_ne_zero P t ω)
  have h := abs_le.mp (log_eulerProduct_quadratic_bound P t ω)
  constructor
  · apply (Real.le_log_iff_exp_le hn).mp
    linarith [h.1]
  · apply (Real.log_le_iff_le_exp hn).mp
    linarith [h.2]

theorem actual_eulerProduct_exp_bounds (x : ℝ) (i : Fin (factorCount x)) (ω : PhaseSpace) :
    Real.exp (primeArgument (primeCutoff x) (firstCoefficient x i) (secondCoefficient x i)
      (fun n => steinhaus n ω)-logRemainderConstant) ≤
        ‖eulerProduct (primeCutoff x) (linePoint (1/2) (frequency x i)) ω‖ ∧
    ‖eulerProduct (primeCutoff x) (linePoint (1/2) (frequency x i)) ω‖ ≤
      Real.exp (primeArgument (primeCutoff x) (firstCoefficient x i) (secondCoefficient x i)
        (fun n => steinhaus n ω)+logRemainderConstant) := by
  simpa only [quadraticPrimeSum_eq_primeArgument] using
    eulerProduct_exp_bounds (primeCutoff x) (frequency x i) ω

end NField.Alignment.HarperEulerLogComparison
