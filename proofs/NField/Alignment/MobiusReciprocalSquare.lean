/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The reciprocal-square Möbius coefficient

This module evaluates the absolutely convergent reciprocal-square Möbius
series at the coefficient used by the continuous secondary term.
-/

namespace NField.Alignment.MobiusReciprocalSquare

open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation
open LSeries ArithmeticFunction

/-- Real reciprocal-square Möbius coefficient. -/
noncomputable def mobiusReciprocalSquare (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2

/-- The reciprocal-square Möbius series has the exact Euler coefficient
`6 / π²`. -/
theorem hasSum_mobiusReciprocalSquare :
    HasSum mobiusReciprocalSquare (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ) : ℂ).re := by norm_num
  have hsumC :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have hproduct :=
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := (2 : ℂ)) hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    riemannZeta_two] at hproduct
  have hpiC : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hvalue :
      L ↗ArithmeticFunction.moebius (2 : ℂ) =
        ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have hcast : ((6 / Real.pi ^ 2 : ℝ) : ℂ) =
        6 / (Real.pi : ℂ) ^ 2 := by
      push_cast
      rfl
    rw [hcast]
    apply (eq_div_iff (pow_ne_zero 2 hpiC)).2
    calc
      L ↗ArithmeticFunction.moebius (2 : ℂ) * (Real.pi : ℂ) ^ 2 =
          6 * (((Real.pi : ℂ) ^ 2 / 6) *
            L ↗ArithmeticFunction.moebius (2 : ℂ)) := by ring
      _ = 6 := by rw [hproduct]; norm_num
  rw [hvalue] at hsumC
  apply Complex.hasSum_ofReal.mp
  refine hsumC.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp [mobiusReciprocalSquare]
  · simp [mobiusReciprocalSquare, LSeries.term_of_ne_zero hn,
      Complex.cpow_ofNat]

theorem summable_mobiusReciprocalSquare :
    Summable mobiusReciprocalSquare :=
  hasSum_mobiusReciprocalSquare.summable

theorem abs_mobiusReciprocalSquare_le_rpow
    {n : ℕ} (hn : 0 < n) :
    |mobiusReciprocalSquare n| ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have hmobius : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold mobiusReciprocalSquare
  rw [abs_div, abs_pow, abs_of_nonneg hnR.le]
  rw [Real.rpow_neg hnR.le]
  have hden : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hmobius hden

theorem shifted_reciprocal_square_tsum_le
    {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) ≤
      1 / (N : ℝ) := by
  calc
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) ≤
        ∫ x : ℝ in Set.Ioi (N : ℝ), x ^ (-2 : ℝ) := by
      change (∑' n : ℕ,
          (fun x : ℝ => x ^ (-2 : ℝ)) ((n + N + 1 : ℕ) : ℝ)) ≤
        ∫ x : ℝ in Set.Ioi (N : ℝ),
          (fun x : ℝ => x ^ (-2 : ℝ)) x
      have hanti : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ))
          (Set.Ici (N : ℝ)) :=
        (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by norm_num : (-2 : ℝ) ≤ 0)).mono
          (Set.Ici_subset_Ioi.2 (by exact_mod_cast hN))
      have hint : MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (N : ℝ)) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) (by exact_mod_cast hN)
      exact hanti.tsum_comp_add_le_integral N hint (by
        intro x hx
        exact Real.rpow_nonneg
          ((Nat.cast_nonneg N).trans (Set.mem_Ioi.mp hx).le) _)
    _ = 1 / (N : ℝ) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) (by exact_mod_cast hN)]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring

theorem mobiusReciprocalSquare_tail_identity (N : ℕ) :
    6 / Real.pi ^ 2 -
        ∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d =
      ∑' n : ℕ, mobiusReciprocalSquare (n + N + 1) := by
  have hsplit := summable_mobiusReciprocalSquare.sum_add_tsum_nat_add (N + 1)
  have hfull := hasSum_mobiusReciprocalSquare.tsum_eq
  have hrange :
      (∑ d ∈ Finset.range (N + 1), mobiusReciprocalSquare d) =
        ∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
      omega
    · intro d hdRange hdIcc
      have hd0 : d = 0 := by
        simp only [Finset.mem_range] at hdRange
        simp only [Finset.mem_Icc, not_and_or, not_le] at hdIcc
        omega
      subst d
      simp [mobiusReciprocalSquare]
  rw [← hfull, ← hsplit, hrange, add_sub_cancel_left]
  apply tsum_congr
  intro n
  congr 1

theorem summable_abs_mobiusReciprocalSquare_tail (N : ℕ) :
    Summable (fun n : ℕ => |mobiusReciprocalSquare (n + N + 1)|) := by
  simpa [add_assoc, add_comm, add_left_comm] using
    (summable_nat_add_iff (f := fun n : ℕ => |mobiusReciprocalSquare n|)
      (N + 1)).mpr summable_mobiusReciprocalSquare.norm

theorem abs_mobiusReciprocalSquare_tsum_le_tsum_abs (N : ℕ) :
    |∑' n : ℕ, mobiusReciprocalSquare (n + N + 1)| ≤
      ∑' n : ℕ, |mobiusReciprocalSquare (n + N + 1)| := by
  have hnorm :
      ‖∑' n : ℕ, mobiusReciprocalSquare (n + N + 1)‖ ≤
        ∑' n : ℕ, ‖mobiusReciprocalSquare (n + N + 1)‖ :=
    norm_tsum_le_tsum_norm (summable_abs_mobiusReciprocalSquare_tail N)
  simpa only [Real.norm_eq_abs] using hnorm

theorem tsum_abs_mobiusReciprocalSquare_tail_le (N : ℕ) :
    (∑' n : ℕ, |mobiusReciprocalSquare (n + N + 1)|) ≤
      ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have habsSummable : Summable (fun n : ℕ =>
      |mobiusReciprocalSquare (n + N + 1)|) :=
    summable_abs_mobiusReciprocalSquare_tail N
  have hpseries : Summable (fun n : ℕ =>
      ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) (N + 1)).mpr
          (Real.summable_nat_rpow.mpr (by norm_num))
  apply habsSummable.tsum_le_tsum _ hpseries
  intro n
  exact abs_mobiusReciprocalSquare_le_rpow (by omega)

theorem abs_mobiusReciprocalSquare_tsum_tail_le (N : ℕ) :
    |∑' n : ℕ, mobiusReciprocalSquare (n + N + 1)| ≤
      ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
  (abs_mobiusReciprocalSquare_tsum_le_tsum_abs N).trans
    (tsum_abs_mobiusReciprocalSquare_tail_le N)

/-- The absolutely convergent tail has the elementary integral-test bound
needed when the finite Möbius sum is replaced by its Euler coefficient. -/
theorem abs_mobiusReciprocalSquare_tail_le
    {N : ℕ} (hN : 1 ≤ N) :
    |6 / Real.pi ^ 2 -
        ∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d| ≤
      1 / (N : ℝ) := by
  rw [mobiusReciprocalSquare_tail_identity]
  calc
    |∑' n : ℕ, mobiusReciprocalSquare (n + N + 1)| ≤
        ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
      abs_mobiusReciprocalSquare_tsum_tail_le N
    _ ≤ 1 / (N : ℝ) := shifted_reciprocal_square_tsum_le hN

/-- Finite reciprocal-square mass is bounded by the exact zeta value. -/
theorem reciprocalSquareFiniteSum_le_zetaTwo (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ^ 2) ≤
      Real.pi ^ 2 / 6 := by
  rw [← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum (Finset.Icc 1 N) (by
    intro d _hd
    positivity)

/-- A single logarithmic-square weight is dominated by a convergent
three-halves `p`-series term. -/
theorem one_add_log_sq_div_sq_le_pseries
    {d : ℕ} (hd : 0 < d) :
    (1 + Real.log d) ^ 2 / (d : ℝ) ^ 2 ≤
      25 * (d : ℝ) ^ (-3 / 2 : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let R : ℝ := (d : ℝ) ^ (1 / 4 : ℝ)
  have hR0 : 0 ≤ R := Real.rpow_nonneg hdR.le _
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_rpow hdOne (by norm_num)
  have hlog : Real.log d ≤ 4 * R := by
    have hbase := Real.log_le_rpow_div hdR.le
      (by norm_num : (0 : ℝ) < 1 / 4)
    dsimp [R]
    convert hbase using 1
    all_goals ring
  have hnum : (1 + Real.log d) ^ 2 ≤ 25 * R ^ 2 := by
    have hlog0 : 0 ≤ Real.log d := Real.log_nonneg hdOne
    nlinarith
  have hden : (0 : ℝ) ≤ ((d : ℝ) ^ 2)⁻¹ := by positivity
  calc
    (1 + Real.log d) ^ 2 / (d : ℝ) ^ 2 ≤
        (25 * R ^ 2) / (d : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = 25 * (d : ℝ) ^ (-3 / 2 : ℝ) := by
      have hrpowSquare : R ^ 2 = (d : ℝ) ^ (1 / 2 : ℝ) := by
        dsimp [R]
        rw [pow_two, ← Real.rpow_add hdR]
        congr 1
        ring
      have hpow : (d : ℝ) ^ 2 = Real.rpow (d : ℝ) (2 : ℝ) :=
        (Real.rpow_natCast (d : ℝ) 2).symm
      rw [hrpowSquare, hpow]
      have hsub := Real.rpow_sub hdR (1 / 2 : ℝ) (2 : ℝ)
      calc
        25 * Real.rpow (d : ℝ) (1 / 2 : ℝ) /
            Real.rpow (d : ℝ) (2 : ℝ) =
            25 * (Real.rpow (d : ℝ) (1 / 2 : ℝ) /
              Real.rpow (d : ℝ) (2 : ℝ)) := by ring
        _ = 25 * Real.rpow (d : ℝ) ((1 / 2 : ℝ) - 2) := by
          exact congrArg (fun x : ℝ => 25 * x) hsub.symm
        _ = 25 * Real.rpow (d : ℝ) (-3 / 2 : ℝ) := by
          congr 2
          ring

/-- All finite logarithmic Möbius moments needed by the transfer are bounded
by one explicit convergent `p`-series, independently of the cutoff. -/
theorem mobiusLogMomentFiniteSum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        |mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2) ≤
      25 * ∑' d : ℕ, (d : ℝ) ^ (-3 / 2 : ℝ) := by
  have hsummable : Summable (fun d : ℕ =>
      25 * (d : ℝ) ^ (-3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 25
  calc
    (∑ d ∈ Finset.Icc 1 N,
        |mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2) ≤
        ∑ d ∈ Finset.Icc 1 N,
          25 * (d : ℝ) ^ (-3 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmobius :
          |mobiusReciprocalSquare d| ≤ 1 / (d : ℝ) ^ 2 := by
        unfold mobiusReciprocalSquare
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        exact div_le_div_of_nonneg_right hmu (by positivity)
      calc
        |mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2 ≤
            (1 / (d : ℝ) ^ 2) * (1 + Real.log d) ^ 2 := by
          gcongr
        _ = (1 + Real.log d) ^ 2 / (d : ℝ) ^ 2 := by ring
        _ ≤ 25 * (d : ℝ) ^ (-3 / 2 : ℝ) :=
          one_add_log_sq_div_sq_le_pseries hdpos
    _ ≤ ∑' d : ℕ, 25 * (d : ℝ) ^ (-3 / 2 : ℝ) := by
      exact hsummable.sum_le_tsum (Finset.Icc 1 N) (by
        intro d _hd
        positivity)
    _ = 25 * ∑' d : ℕ, (d : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [tsum_mul_left]

end NField.Alignment.MobiusReciprocalSquare
