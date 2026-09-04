/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.WeightedFractionalPartTransfer
import NField.Alignment.MobiusReciprocalSquare

/-!
# Fractional-floor Möbius asymptotic

This module performs the finite Möbius transfer from the uniform rational
weighted fractional-part estimate to the continuous secondary coefficient.
-/

namespace NField.Alignment.FractionalMobiusAsymptotic

open scoped BigOperators ArithmeticFunction.Moebius
open NField.Alignment.ReducedHarmonicMobius
open NField.Alignment.SecondaryCapacityLedger
open NField.Alignment.WeightedFractionalPartTransfer
open NField.Alignment.MobiusReciprocalSquare

noncomputable def fractionalMobiusRemainderScale (N : ℕ) : ℝ :=
  Real.rpow (Real.log N) (5 / 3 : ℝ)

noncomputable def floorLogMobiusMain (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    mobiusReciprocalSquare d *
      ((1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2)

theorem abs_mobiusReciprocalSquare_le_inv_sq
    {d : ℕ} (hd : 0 < d) :
    |mobiusReciprocalSquare d| ≤ 1 / (d : ℝ) ^ 2 := by
  unfold mobiusReciprocalSquare
  rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact div_le_div_of_nonneg_right hmu (by positivity)

theorem one_add_log_mul_distributionScale_le
    {N d : ℕ} (hN : 3 ≤ N) (hd : 0 < d) (hactive : 3 * d ≤ N) :
    (1 + Real.log ((N / d : ℕ) : ℝ)) *
        (1 + fractionalDistributionScale N d) ≤
      4 * fractionalMobiusRemainderScale N := by
  have hQ : 3 ≤ N / d :=
    (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hactive)
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogQ0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N / d by omega))
  have hlogQle :
      Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < N / d by omega)
    · exact_mod_cast Nat.div_le_self N d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratioOne : (1 : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    simpa using (show (d : ℝ) ≤ (N : ℝ) by exact_mod_cast (show d ≤ N by omega))
  have hratioN : (N : ℝ) / (d : ℝ) ≤ (N : ℝ) := by
    rw [div_le_iff₀ hdR]
    nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
  have hlogRatio :
      Real.log ((N : ℝ) / (d : ℝ)) ≤ Real.log N :=
    Real.log_le_log (by positivity) hratioN
  have hscaleLe : fractionalDistributionScale N d ≤
      Real.rpow (Real.log N) (2 / 3 : ℝ) := by
    unfold fractionalDistributionScale
    exact Real.rpow_le_rpow (Real.log_nonneg hratioOne) hlogRatio (by norm_num)
  have hrpow23 : (1 : ℝ) ≤
      Real.rpow (Real.log N) (2 / 3 : ℝ) :=
    Real.one_le_rpow hlogN (by norm_num)
  have hfactorOne :
      1 + Real.log ((N / d : ℕ) : ℝ) ≤ 2 * Real.log N := by
    linarith
  have hfactorTwo :
      1 + fractionalDistributionScale N d ≤
        2 * Real.rpow (Real.log N) (2 / 3 : ℝ) := by
    linarith
  have hmul := mul_le_mul hfactorOne hfactorTwo
    (by have := fractionalDistributionScale_nonneg hd (by omega : d ≤ N)
        linarith)
    (by linarith)
  calc
    (1 + Real.log ((N / d : ℕ) : ℝ)) *
        (1 + fractionalDistributionScale N d) ≤
      (2 * Real.log N) *
        (2 * Real.rpow (Real.log N) (2 / 3 : ℝ)) := hmul
    _ = 4 * fractionalMobiusRemainderScale N := by
      unfold fractionalMobiusRemainderScale
      have hadd := Real.rpow_add (show 0 < Real.log N by linarith)
        (1 : ℝ) (2 / 3 : ℝ)
      rw [Real.rpow_one] at hadd
      calc
        (2 * Real.log N) *
            (2 * Real.rpow (Real.log N) (2 / 3 : ℝ)) =
          4 * (Real.log N * Real.rpow (Real.log N) (2 / 3 : ℝ)) := by
            ring
        _ = 4 * Real.rpow (Real.log N) (1 + 2 / 3 : ℝ) := by
          exact congrArg (fun x : ℝ => 4 * x) hadd.symm
        _ = 4 * Real.rpow (Real.log N) (5 / 3 : ℝ) := by
          congr 2
          ring

theorem inactive_weighted_error_le
    {N d : ℕ} (hN : 3 ≤ N) (hd : 0 < d) (hdN : d ≤ N)
    (hinactive : ¬ 3 * d ≤ N) :
    |weightedFractionalPartsAtQuotient N d -
        (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
      2 * fractionalMobiusRemainderScale N := by
  have hQpos : 0 < N / d := Nat.div_pos hdN hd
  have hQle : N / d ≤ 2 := by
    by_contra h
    have hQ : 3 ≤ N / d := by omega
    exact hinactive ((Nat.le_div_iff_mul_le hd).1 hQ)
  have hW0 := weightedFractionalPartsAtQuotient_nonneg N hd
  have hW1 := weightedFractionalPartsAtQuotient_le_one_of_quotient_le_two
    N hd hQle
  have hlog0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N / d by omega))
  have hlogOne : Real.log ((N / d : ℕ) : ℝ) ≤ 1 := by
    calc
      Real.log ((N / d : ℕ) : ℝ) ≤ Real.log 2 :=
        Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
      _ ≤ 1 := (Real.log_two_lt_d9).le.trans (by norm_num)
  have hraw :
      |weightedFractionalPartsAtQuotient N d -
          (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg
      (Real.log ((N / d : ℕ) : ℝ))]
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hscaleOne : (1 : ℝ) ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.one_le_rpow hlogN (by norm_num)
  exact hraw.trans (by nlinarith)

/-- The exact finite Möbius transform differs from its quotient-log main sum
by the manuscript's remainder scale. -/
theorem exactMobiusFractionalTransform_sub_floorLogMobiusMain
    (hSV : SaffariVaughanDistributionEstimate) :
    EventualErrorBound exactMobiusFractionalTransform floorLogMobiusMain
      fractionalMobiusRemainderScale := by
  rcases rational_floor_weighted_fractional_parts_of_saffari_vaughan hSV with
    ⟨C, hC, hweighted⟩
  refine ⟨(4 * C + 2) * (Real.pi ^ 2 / 6), by positivity, 3, ?_⟩
  intro N hN
  unfold exactMobiusFractionalTransform floorLogMobiusMain
  rw [← Finset.sum_sub_distrib]
  have hscale0 : 0 ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (mobiusReciprocalSquare d * weightedFractionalPartsAtQuotient N d -
          mobiusReciprocalSquare d *
            ((1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2))| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |mobiusReciprocalSquare d *
          (weightedFractionalPartsAtQuotient N d -
            (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2)| := by
      calc
        _ = |∑ d ∈ Finset.Icc 1 N,
            mobiusReciprocalSquare d *
              (weightedFractionalPartsAtQuotient N d -
                (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        ((4 * C + 2) * fractionalMobiusRemainderScale N) /
          (d : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd := (Finset.mem_Icc.mp hdmem).1
      have hdN := (Finset.mem_Icc.mp hdmem).2
      rw [abs_mul]
      have hcoefficient := abs_mobiusReciprocalSquare_le_inv_sq hd
      by_cases hactive : 3 * d ≤ N
      · have herr := hweighted N d hd hactive
        have henvelope := one_add_log_mul_distributionScale_le
          hN hd hactive
        have herror :
            |weightedFractionalPartsAtQuotient N d -
              (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
              4 * C * fractionalMobiusRemainderScale N := by
          calc
            _ ≤ C * ((1 + Real.log ((N / d : ℕ) : ℝ)) *
                (1 + fractionalDistributionScale N d)) := by
              simpa [mul_assoc] using herr
            _ ≤ C * (4 * fractionalMobiusRemainderScale N) := by
              gcongr
            _ = 4 * C * fractionalMobiusRemainderScale N := by ring
        calc
          |mobiusReciprocalSquare d| *
              |weightedFractionalPartsAtQuotient N d -
                (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
            (1 / (d : ℝ) ^ 2) *
              (4 * C * fractionalMobiusRemainderScale N) := by gcongr
          _ ≤ ((4 * C + 2) * fractionalMobiusRemainderScale N) /
              (d : ℝ) ^ 2 := by
            have hdR : (0 : ℝ) < d := by exact_mod_cast hd
            field_simp [hdR.ne']
            nlinarith
      · have herror := inactive_weighted_error_le hN hd hdN hactive
        calc
          |mobiusReciprocalSquare d| *
              |weightedFractionalPartsAtQuotient N d -
                (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
            (1 / (d : ℝ) ^ 2) *
              (2 * fractionalMobiusRemainderScale N) := by gcongr
          _ ≤ ((4 * C + 2) * fractionalMobiusRemainderScale N) /
              (d : ℝ) ^ 2 := by
            have hdR : (0 : ℝ) < d := by exact_mod_cast hd
            field_simp [hdR.ne']
            nlinarith
    _ = ((4 * C + 2) * fractionalMobiusRemainderScale N) *
        ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ ≤ ((4 * C + 2) * fractionalMobiusRemainderScale N) *
        (Real.pi ^ 2 / 6) := by
      gcongr
      exact reciprocalSquareFiniteSum_le_zetaTwo N
    _ = ((4 * C + 2) * (Real.pi ^ 2 / 6)) *
        fractionalMobiusRemainderScale N := by ring

noncomputable def rationalLogMobiusMain (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    mobiusReciprocalSquare d *
      ((1 / 4 : ℝ) *
        (Real.log N - Real.log d) ^ 2)

/-- Replacing the exact real quotient by its natural quotient changes a
logarithmic square by at most a linear logarithm. -/
theorem abs_floorQuotientLog_sq_sub_logRatio_sq_le
    {N d : ℕ} (hN : 3 ≤ N) (hd : 0 < d) (hdN : d ≤ N) :
    |Real.log ((N / d : ℕ) : ℝ) ^ 2 -
        (Real.log N - Real.log d) ^ 2| ≤
      2 * Real.log N := by
  let Q : ℕ := N / d
  let X : ℝ := (N : ℝ) / (d : ℝ)
  let q : ℝ := Real.log (Q : ℝ)
  let x : ℝ := Real.log X
  let L : ℝ := Real.log N
  have hQpos : 0 < Q := Nat.div_pos hdN hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQleX : (Q : ℝ) ≤ X := by
    dsimp [Q, X]
    rw [le_div_iff₀ hdR]
    exact_mod_cast (by simpa [Nat.mul_comm] using Nat.mul_div_le N d)
  have hdivision := Nat.mod_add_div N d
  have hmod := Nat.mod_lt N hd
  have hNXnat : N < d * (Q + 1) := by
    dsimp [Q]
    calc
      N = N % d + d * (N / d) := hdivision.symm
      _ < d + d * (N / d) := Nat.add_lt_add_right hmod _
      _ = d * (N / d + 1) := by ring
  have hXlt : X < (Q : ℝ) + 1 := by
    dsimp [X]
    rw [div_lt_iff₀ hdR]
    exact_mod_cast (by simpa [Nat.mul_comm] using hNXnat)
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
  have hXleTwoQ : X ≤ 2 * (Q : ℝ) := by
    linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.log_nonneg hQone
  have hqx : q ≤ x := by
    dsimp [q, x]
    exact Real.log_le_log (by exact_mod_cast hQpos) hQleX
  have hxqOne : x - q ≤ 1 := by
    have hlogTwoQ : x ≤ Real.log (2 * (Q : ℝ)) := by
      dsimp [x]
      exact Real.log_le_log (by positivity) hXleTwoQ
    have hlogMul : Real.log (2 * (Q : ℝ)) =
        Real.log 2 + Real.log (Q : ℝ) := by
      rw [Real.log_mul (by norm_num) (by exact_mod_cast hQpos.ne')]
    have hlogTwo : Real.log 2 ≤ 1 :=
      (Real.log_two_lt_d9).le.trans (by norm_num)
    dsimp [q] at hlogTwoQ ⊢
    rw [hlogMul] at hlogTwoQ
    linarith
  have hXone : (1 : ℝ) ≤ X := hQone.trans hQleX
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg hXone
  have hXN : X ≤ (N : ℝ) := by
    dsimp [X]
    rw [div_le_iff₀ hdR]
    nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
  have hxL : x ≤ L := by
    dsimp [x, L]
    exact Real.log_le_log (by positivity) hXN
  have hqL : q ≤ L := hqx.trans hxL
  have hratioLog : x = L - Real.log d := by
    dsimp [x, X, L]
    exact Real.log_div hNpos.ne' hdR.ne'
  have hsquare : |q ^ 2 - x ^ 2| ≤ 2 * L := by
    rw [abs_of_nonpos (by nlinarith : q ^ 2 - x ^ 2 ≤ 0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hqx) (add_nonneg hx0 hq0)]
  simpa [Q, q, hratioLog] using hsquare

/-- Natural-quotient logarithms and exact rational logarithms give the same
Möbius main sum at the target scale. -/
theorem floorLogMobiusMain_sub_rationalLogMobiusMain :
    EventualErrorBound floorLogMobiusMain rationalLogMobiusMain
      fractionalMobiusRemainderScale := by
  refine ⟨Real.pi ^ 2 / 12, by positivity, 3, ?_⟩
  intro N hN
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogScale : Real.log N ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.self_le_rpow_of_one_le hlogN (by norm_num)
  unfold floorLogMobiusMain rationalLogMobiusMain
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (mobiusReciprocalSquare d *
            ((1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2) -
          mobiusReciprocalSquare d *
            ((1 / 4 : ℝ) * (Real.log N - Real.log d) ^ 2))| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |mobiusReciprocalSquare d| * ((1 / 2 : ℝ) * Real.log N) := by
      calc
        _ ≤ ∑ d ∈ Finset.Icc 1 N,
            |mobiusReciprocalSquare d *
              ((1 / 4 : ℝ) *
                (Real.log ((N / d : ℕ) : ℝ) ^ 2 -
                  (Real.log N - Real.log d) ^ 2))| := by
          calc
            _ = |∑ d ∈ Finset.Icc 1 N,
                mobiusReciprocalSquare d * ((1 / 4 : ℝ) *
                  (Real.log ((N / d : ℕ) : ℝ) ^ 2 -
                    (Real.log N - Real.log d) ^ 2))| := by
              congr 1
              apply Finset.sum_congr rfl
              intro d _hd
              ring
            _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hdmem
          have hd := (Finset.mem_Icc.mp hdmem).1
          have hdN := (Finset.mem_Icc.mp hdmem).2
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
          have hsquare := abs_floorQuotientLog_sq_sub_logRatio_sq_le hN hd hdN
          nlinarith [abs_nonneg (mobiusReciprocalSquare d)]
    _ ≤ (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ^ 2) *
        ((1 / 2 : ℝ) * Real.log N) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hdmem
      gcongr
      exact abs_mobiusReciprocalSquare_le_inv_sq
        (Finset.mem_Icc.mp hdmem).1
    _ ≤ (Real.pi ^ 2 / 6) * ((1 / 2 : ℝ) * Real.log N) := by
      gcongr
      exact reciprocalSquareFiniteSum_le_zetaTwo N
    _ ≤ (Real.pi ^ 2 / 12) * fractionalMobiusRemainderScale N := by
      nlinarith [Real.pi_pos]

noncomputable def finiteEulerMobiusMain (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    mobiusReciprocalSquare d *
      ((1 / 4 : ℝ) * Real.log N ^ 2)

/-- The logarithmic first and second Möbius moments contribute only a linear
logarithm, hence lie below the target remainder scale. -/
theorem rationalLogMobiusMain_sub_finiteEulerMobiusMain :
    EventualErrorBound rationalLogMobiusMain finiteEulerMobiusMain
      fractionalMobiusRemainderScale := by
  let M : ℝ := 25 * ∑' d : ℕ, (d : ℝ) ^ (-3 / 2 : ℝ)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨2 * M, by positivity, 3, ?_⟩
  intro N hN
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hscaleOne : (1 : ℝ) ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.one_le_rpow hlogN (by norm_num)
  have hlogScale : Real.log N ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.self_le_rpow_of_one_le hlogN (by norm_num)
  unfold rationalLogMobiusMain finiteEulerMobiusMain
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (mobiusReciprocalSquare d *
            ((1 / 4 : ℝ) * (Real.log N - Real.log d) ^ 2) -
          mobiusReciprocalSquare d *
            ((1 / 4 : ℝ) * Real.log N ^ 2))| ≤
      ∑ d ∈ Finset.Icc 1 N,
        (3 / 4 : ℝ) * (1 + Real.log N) *
          (|mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2) := by
      calc
        _ = |∑ d ∈ Finset.Icc 1 N,
            mobiusReciprocalSquare d * (1 / 4 : ℝ) *
              ((Real.log N - Real.log d) ^ 2 - Real.log N ^ 2)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ ≤ ∑ d ∈ Finset.Icc 1 N,
            |mobiusReciprocalSquare d * (1 / 4 : ℝ) *
              ((Real.log N - Real.log d) ^ 2 - Real.log N ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hdmem
          have hd := (Finset.mem_Icc.mp hdmem).1
          have hdN := (Finset.mem_Icc.mp hdmem).2
          have hlogd0 : 0 ≤ Real.log d :=
            Real.log_nonneg (by exact_mod_cast hd)
          have hlogdN : Real.log d ≤ Real.log N :=
            Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdN)
          have hinner :
              |(Real.log N - Real.log d) ^ 2 - Real.log N ^ 2| ≤
                3 * (1 + Real.log N) * (1 + Real.log d) ^ 2 := by
            have hsign :
                (Real.log N - Real.log d) ^ 2 - Real.log N ^ 2 ≤ 0 := by
              nlinarith
            rw [abs_of_nonpos hsign]
            nlinarith [mul_nonneg (show 0 ≤ Real.log N by linarith) hlogd0,
              sq_nonneg (1 + Real.log d)]
          rw [abs_mul, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
          have hfactor0 :
              0 ≤ |mobiusReciprocalSquare d| * (1 / 4 : ℝ) := by
            positivity
          have hmul := mul_le_mul_of_nonneg_left hinner hfactor0
          calc
            |mobiusReciprocalSquare d| * (1 / 4 : ℝ) *
                |(Real.log N - Real.log d) ^ 2 - Real.log N ^ 2| ≤
              (|mobiusReciprocalSquare d| * (1 / 4 : ℝ)) *
                (3 * (1 + Real.log N) * (1 + Real.log d) ^ 2) := hmul
            _ = (3 / 4 : ℝ) * (1 + Real.log N) *
                (|mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2) := by ring
    _ = (3 / 4 : ℝ) * (1 + Real.log N) *
        ∑ d ∈ Finset.Icc 1 N,
          (|mobiusReciprocalSquare d| * (1 + Real.log d) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (3 / 4 : ℝ) * (1 + Real.log N) * M := by
      gcongr
      exact mobiusLogMomentFiniteSum_le N
    _ ≤ (2 * M) * fractionalMobiusRemainderScale N := by
      nlinarith

/-- The finite reciprocal-square coefficient differs from `6/π²` by a
reciprocal tail, small enough even after multiplication by `log(N)^2`. -/
theorem finiteEulerMobiusMain_sub_fractionalFloorMain :
    EventualErrorBound finiteEulerMobiusMain fractionalFloorMain
      fractionalMobiusRemainderScale := by
  refine ⟨1 / 4, by norm_num, 3, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogNonneg : 0 ≤ Real.log N := by linarith
  have hlogLeN : Real.log N ≤ (N : ℝ) := by
    have hbase := Real.log_le_sub_one_of_pos hNR
    linarith
  have hlogScale : Real.log N ≤ fractionalMobiusRemainderScale N := by
    unfold fractionalMobiusRemainderScale
    exact Real.self_le_rpow_of_one_le hlogN (by norm_num)
  have hsquareDiv : Real.log N ^ 2 / (N : ℝ) ≤
      fractionalMobiusRemainderScale N := by
    rw [div_le_iff₀ hNR]
    nlinarith [mul_le_mul hlogLeN hlogScale hlogNonneg
      (show 0 ≤ (N : ℝ) by positivity)]
  have htail := abs_mobiusReciprocalSquare_tail_le
    (show 1 ≤ N by omega)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold finiteEulerMobiusMain fractionalFloorMain
  rw [← Finset.sum_mul]
  have hcoefficient :
      (1 / (4 * Real.pi ^ 2 / 6) : ℝ) =
        (6 / Real.pi ^ 2) * (1 / 4 : ℝ) := by
    field_simp [hpi]
  rw [hcoefficient]
  rw [show
    (∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d) *
          ((1 / 4 : ℝ) * Real.log N ^ 2) -
        (6 / Real.pi ^ 2) * (1 / 4 : ℝ) * Real.log N ^ 2 =
      (1 / 4 : ℝ) * Real.log N ^ 2 *
        ((∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d) -
          6 / Real.pi ^ 2) by ring]
  rw [abs_mul, abs_of_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg _))]
  have htail' :
      |(∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d) -
          6 / Real.pi ^ 2| ≤ 1 / (N : ℝ) := by
    simpa [abs_sub_comm] using htail
  calc
    (1 / 4 : ℝ) * Real.log N ^ 2 *
        |(∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d) -
          6 / Real.pi ^ 2| ≤
      (1 / 4 : ℝ) * (Real.log N ^ 2 / (N : ℝ)) := by
      have hfactor : 0 ≤ (1 / 4 : ℝ) * Real.log N ^ 2 := by positivity
      calc
        (1 / 4 : ℝ) * Real.log N ^ 2 *
            |(∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d) -
              6 / Real.pi ^ 2| ≤
          ((1 / 4 : ℝ) * Real.log N ^ 2) * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left htail' hfactor
        _ = (1 / 4 : ℝ) * (Real.log N ^ 2 / (N : ℝ)) := by ring
    _ ≤ (1 / 4 : ℝ) * fractionalMobiusRemainderScale N := by
      gcongr

/-- Complete finite Möbius transfer from quotient logarithms to the exact
continuous secondary coefficient. -/
theorem floorLogMobiusMain_asymptotic :
    EventualErrorBound floorLogMobiusMain fractionalFloorMain
      fractionalMobiusRemainderScale := by
  rcases floorLogMobiusMain_sub_rationalLogMobiusMain with
    ⟨C₁, hC₁, N₁, h₁⟩
  rcases rationalLogMobiusMain_sub_finiteEulerMobiusMain with
    ⟨C₂, hC₂, N₂, h₂⟩
  rcases finiteEulerMobiusMain_sub_fractionalFloorMain with
    ⟨C₃, hC₃, N₃, h₃⟩
  refine ⟨C₁ + C₂ + C₃, by positivity, max N₁ (max N₂ N₃), ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans
    ((le_max_right N₁ (max N₂ N₃)).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans
    ((le_max_right N₁ (max N₂ N₃)).trans hN)
  calc
    |floorLogMobiusMain N - fractionalFloorMain N| ≤
      |floorLogMobiusMain N - rationalLogMobiusMain N| +
        |rationalLogMobiusMain N - finiteEulerMobiusMain N| +
        |finiteEulerMobiusMain N - fractionalFloorMain N| := by
      calc
        _ ≤ |floorLogMobiusMain N - rationalLogMobiusMain N| +
            |rationalLogMobiusMain N - fractionalFloorMain N| :=
          abs_sub_le _ _ _
        _ ≤ |floorLogMobiusMain N - rationalLogMobiusMain N| +
            (|rationalLogMobiusMain N - finiteEulerMobiusMain N| +
              |finiteEulerMobiusMain N - fractionalFloorMain N|) := by
          linarith [abs_sub_le (rationalLogMobiusMain N)
            (finiteEulerMobiusMain N) (fractionalFloorMain N)]
        _ = _ := by ring
    _ ≤ C₁ * fractionalMobiusRemainderScale N +
        C₂ * fractionalMobiusRemainderScale N +
        C₃ * fractionalMobiusRemainderScale N := by
      exact add_le_add (add_le_add (h₁ N hN₁) (h₂ N hN₂)) (h₃ N hN₃)
    _ = (C₁ + C₂ + C₃) * fractionalMobiusRemainderScale N := by ring

/-- The complete exact Möbius transform has the coefficient `3/(2π²)` and
the manuscript's `log^(5/3)` remainder. -/
theorem exactMobiusFractionalTransform_asymptotic
    (hSV : SaffariVaughanDistributionEstimate) :
    EventualErrorBound exactMobiusFractionalTransform fractionalFloorMain
      fractionalMobiusRemainderScale := by
  rcases exactMobiusFractionalTransform_sub_floorLogMobiusMain hSV with
    ⟨C₁, hC₁, N₁, h₁⟩
  rcases floorLogMobiusMain_asymptotic with ⟨C₂, hC₂, N₂, h₂⟩
  refine ⟨C₁ + C₂, by positivity, max N₁ N₂, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  calc
    |exactMobiusFractionalTransform N - fractionalFloorMain N| ≤
      |exactMobiusFractionalTransform N - floorLogMobiusMain N| +
        |floorLogMobiusMain N - fractionalFloorMain N| :=
      abs_sub_le _ _ _
    _ ≤ C₁ * fractionalMobiusRemainderScale N +
        C₂ * fractionalMobiusRemainderScale N :=
      add_le_add (h₁ N hN₁) (h₂ N hN₂)
    _ = (C₁ + C₂) * fractionalMobiusRemainderScale N := by ring

/-- The manuscript's fractional-floor asymptotic follows from its exact finite
Möbius reduction and the source distribution theorem. -/
theorem fractionalFloorTerm_asymptotic
    (hSV : SaffariVaughanDistributionEstimate) :
    EventualErrorBound fractionalFloorTerm fractionalFloorMain
      fractionalMobiusRemainderScale := by
  rcases exactMobiusFractionalTransform_asymptotic hSV with
    ⟨C, hC, N₀, hbound⟩
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN
  rw [mobius_reduction]
  exact hbound N hN

end NField.Alignment.FractionalMobiusAsymptotic
