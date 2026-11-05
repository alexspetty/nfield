/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerSingularity
import NField.Alignment.FractionalMobiusAsymptotic

/-!
# The truncated stationary age

The exact harmonic-square identity and an elementary absolutely convergent
Mobius transfer prove the logarithmic-square stationary centering. No
fractional-part distribution estimate is assumed or used.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionStationaryAgeAsymptotic

open scoped BigOperators
open Filter
open CollisionRemainderDynamics CollisionMassReadout SecondaryCapacityLedger
open ReducedHarmonicMobius MobiusReciprocalSquare

def harmonicSquareSum (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ)^2

theorem harmonic_cross_sum (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (harmonic (j-1) : ℝ) / j) =
      ((harmonic M : ℝ)^2 - harmonicSquareSum M) / 2 := by
  induction M with
  | zero => simp [harmonicSquareSum]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hsq : harmonicSquareSum (M+1) =
        harmonicSquareSum M + 1 / ((M+1 : ℕ) : ℝ)^2 := by
      unfold harmonicSquareSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hsq, harmonic_succ]
    push_cast
    field_simp
    ring

def firstMoment (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 M, (k : ℝ) * collisionWeight k

theorem firstMoment_moebius (M : ℕ) :
    firstMoment M = (1/2 : ℝ) * ∑ d ∈ Finset.Icc 1 M,
      mobiusReciprocalSquare d *
        ((harmonic (M/d) : ℝ)^2 - harmonicSquareSum (M/d)) := by
  have hterm (k : ℕ) (hk : 0 < k) :
      (k : ℝ) * collisionWeight k = ∑ d ∈ k.divisors,
        mobiusReciprocalSquare d * (harmonic (k/d-1) : ℝ) / (k/d : ℕ) := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [collisionWeight, reducedHarmonicStar_moebius hk, Finset.sum_div,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdk := (Nat.mem_divisors.mp hd).1
    have hdpos := Nat.pos_of_dvd_of_pos hdk hk
    have hnpos := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
    have hde : (k : ℝ) = (d : ℝ) * ((k/d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdk).symm
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hnR : ((k/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    unfold mobiusReciprocalSquare
    rw [hde]
    field_simp
  have hf : firstMoment M = ∑ k ∈ Finset.Icc 1 M,
      ∑ d ∈ k.divisors, mobiusReciprocalSquare d *
        (harmonic (k/d-1) : ℝ) / (k/d : ℕ) := by
    exact Finset.sum_congr rfl (fun k hk => hterm k (Finset.mem_Icc.mp hk).1)
  rw [hf]
  rw [sum_divisor_triangle M
    (fun d n => mobiusReciprocalSquare d * (harmonic (n-1) : ℝ) / n)]
  simp_rw [mul_div_assoc, ← Finset.mul_sum, harmonic_cross_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem harmonic_square_log_error {n : ℕ} (hn : 0 < n) :
    |(harmonic n : ℝ)^2 - harmonicSquareSum n - Real.log n ^ 2| ≤
      2 * Real.log n + 1 + Real.pi^2/6 := by
  have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hh0 := harmonic_nonneg n
  have hhl := harmonic_le_one_add_log n
  have hlh : Real.log (n : ℝ) ≤ (harmonic n : ℝ) :=
    (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast Nat.le_succ n)).trans
      (log_add_one_le_harmonic n)
  have hs0 : 0 ≤ harmonicSquareSum n := by unfold harmonicSquareSum; positivity
  have hs := reciprocalSquareFiniteSum_le_zetaTwo n
  change harmonicSquareSum n ≤ Real.pi^2/6 at hs
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ((harmonic n : ℝ) - Real.log n),
    mul_nonneg (sub_nonneg.mpr hlh) (add_nonneg hh0 hl0)]

theorem quotient_harmonic_error {M d : ℕ} (hM : 3 ≤ M)
    (hd : 0 < d) (hdM : d ≤ M) :
    |(harmonic (M/d) : ℝ)^2 - harmonicSquareSum (M/d) - Real.log M^2| ≤
      (7 + Real.pi^2/6) * (1 + Real.log M) * (1 + Real.log d)^2 := by
  have hq : 0 < M/d := Nat.div_pos hdM hd
  have hqM : M/d ≤ M := Nat.div_le_self _ _
  have hld0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hLM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hldM : Real.log (d : ℝ) ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdM)
  have hlq : Real.log ((M/d : ℕ) : ℝ) ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqM)
  have he1 := harmonic_square_log_error hq
  have he2 := FractionalMobiusAsymptotic.abs_floorQuotientLog_sq_sub_logRatio_sq_le
    hM hd hdM
  have he3 : |(Real.log M - Real.log d)^2 - Real.log M^2| ≤
      2 * Real.log M * Real.log d := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hLM hld0]
  have htri := abs_sub_le ((harmonic (M/d) : ℝ)^2 - harmonicSquareSum (M/d))
    (Real.log ((M/d : ℕ) : ℝ)^2) (Real.log M^2)
  have htri2 := abs_sub_le (Real.log ((M/d : ℕ) : ℝ)^2)
    ((Real.log M - Real.log d)^2) (Real.log M^2)
  have hW1 : 1 ≤ (1 + Real.log d)^2 := by nlinarith
  have hWt : Real.log d ≤ (1 + Real.log d)^2 := by nlinarith [sq_nonneg (Real.log d)]
  have hbase : 4 * Real.log M + 1 + Real.pi^2/6 ≤
      (5 + Real.pi^2/6) * (1 + Real.log M) := by
    nlinarith [mul_nonneg (sq_nonneg Real.pi) hLM]
  calc
    _ ≤ 4 * Real.log M + 1 + Real.pi^2/6 + 2 * Real.log M * Real.log d := by
      linarith
    _ ≤ (5 + Real.pi^2/6) * (1 + Real.log M) * (1 + Real.log d)^2 +
        2 * (1 + Real.log M) * (1 + Real.log d)^2 := by
      apply add_le_add
      · exact hbase.trans (le_mul_of_one_le_right (by positivity) hW1)
      · gcongr
        · linarith
    _ = _ := by ring

def momentConstant : ℝ := 25 * ∑' d : ℕ, (d : ℝ)^(-3/2 : ℝ)

theorem momentConstant_nonneg : 0 ≤ momentConstant := by unfold momentConstant; positivity

theorem firstMoment_finite_main_error {M : ℕ} (hM : 3 ≤ M) :
    |firstMoment M - (Real.log M^2 / 2) *
      ∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d| ≤
      ((7 + Real.pi^2/6) * momentConstant / 2) * (1 + Real.log M) := by
  rw [firstMoment_moebius]
  have he : (1/2 : ℝ) * (∑ d ∈ Finset.Icc 1 M,
      mobiusReciprocalSquare d * ((harmonic (M/d) : ℝ)^2 - harmonicSquareSum (M/d))) -
      (Real.log M^2/2) * (∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d) =
      (1/2 : ℝ) * ∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d *
        ((harmonic (M/d) : ℝ)^2 - harmonicSquareSum (M/d) - Real.log M^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have hLM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  calc
    _ ≤ (1/2 : ℝ) * ∑ d ∈ Finset.Icc 1 M, |mobiusReciprocalSquare d| *
        ((7 + Real.pi^2/6) * (1 + Real.log M) * (1 + Real.log d)^2) := by
      gcongr
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      gcongr
      exact quotient_harmonic_error hM (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    _ = ((7 + Real.pi^2/6) / 2) * (1 + Real.log M) *
        ∑ d ∈ Finset.Icc 1 M, |mobiusReciprocalSquare d| * (1 + Real.log d)^2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((7 + Real.pi^2/6) / 2) * (1 + Real.log M) * momentConstant := by
      gcongr
      exact mobiusLogMomentFiniteSum_le M
    _ = _ := by ring

theorem firstMoment_main_error {M : ℕ} (hM : 3 ≤ M) :
    |firstMoment M - (3 / Real.pi^2) * Real.log M^2| ≤
      (((7 + Real.pi^2/6) * momentConstant / 2) + 1) * (1 + Real.log M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hLM : Real.log (M : ℝ) ≤ M := by
    linarith [Real.log_le_sub_one_of_pos hMpos]
  have htail : |(∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d) - 6/Real.pi^2| ≤
      1/(M : ℝ) := by
    rw [abs_sub_comm]
    exact abs_mobiusReciprocalSquare_tail_le (by omega)
  have htail2 : |(Real.log M^2 / 2) * (∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d) -
      (3/Real.pi^2) * Real.log M^2| ≤ Real.log M / 2 := by
    have he : (Real.log M^2 / 2) * (∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d) -
        (3/Real.pi^2) * Real.log M^2 = (Real.log M^2/2) *
          ((∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d) - 6/Real.pi^2) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log M^2/2)]
    calc
      _ ≤ (Real.log M^2/2) * (1/(M : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ Real.log M/2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        have hmul := mul_le_mul_of_nonneg_left hLM hL0
        field_simp
        nlinarith
  have he := firstMoment_finite_main_error hM
  have ht := abs_sub_le (firstMoment M)
    ((Real.log M^2 / 2) * ∑ d ∈ Finset.Icc 1 M, mobiusReciprocalSquare d)
    ((3/Real.pi^2)*Real.log M^2)
  nlinarith

theorem stationaryAge_firstMoment (M : ℕ) :
    stationaryAge collisionWeight M =
      (firstMoment M - ∑ k ∈ Finset.Icc 1 M, collisionWeight k) / 3 := by
  have he : (∑ k ∈ Finset.Icc 2 M, collisionWeight k * ((k : ℝ)-1)) =
      ∑ k ∈ Finset.Icc 1 M, collisionWeight k * ((k : ℝ)-1) := by
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
    · intro k hk hnot
      have hk' := Finset.mem_Icc.mp hk
      have hk1 : k = 1 := by simp only [Finset.mem_Icc] at hnot; omega
      subst k
      simp
  rw [stationaryAge, he]
  unfold firstMoment
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  simp_rw [mul_comm (collisionWeight _) (_ : ℝ)]
  ring

theorem stationaryAge_main_error {M : ℕ} (hM : 3 ≤ M) :
    |stationaryAge collisionWeight M - Real.log M^2 / Real.pi^2| ≤
      ((((7 + Real.pi^2/6) * momentConstant / 2) + 2) / 3) * (1 + Real.log M) := by
  have hL0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hw0 : 0 ≤ ∑ k ∈ Finset.Icc 1 M, collisionWeight k :=
    Finset.sum_nonneg (fun k _ => collisionWeight_nonneg k)
  have hw1 : (∑ k ∈ Finset.Icc 1 M, collisionWeight k) ≤ 1 := by
    rw [← collisionWeight_tsum]
    exact collisionWeight_summable.sum_le_tsum _ (fun k _ => collisionWeight_nonneg k)
  rw [stationaryAge_firstMoment]
  have he : (firstMoment M - ∑ k ∈ Finset.Icc 1 M, collisionWeight k) / 3 -
      Real.log M^2/Real.pi^2 = ((firstMoment M - (3/Real.pi^2)*Real.log M^2) -
        ∑ k ∈ Finset.Icc 1 M, collisionWeight k) / 3 := by ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have ht := abs_sub (firstMoment M - (3/Real.pi^2)*Real.log M^2)
    (∑ k ∈ Finset.Icc 1 M, collisionWeight k)
  rw [abs_of_nonneg hw0] at ht
  have hb := firstMoment_main_error hM
  linarith

/-- The stated stationary-age asymptotic with its exact leading coefficient. -/
theorem stationaryAge_isBigO_log :
    Asymptotics.IsBigO atTop
      (fun M : ℕ => stationaryAge collisionWeight M - Real.log M^2/Real.pi^2)
      (fun M : ℕ => Real.log (2*(M : ℝ))) := by
  let C : ℝ := (((7 + Real.pi^2/6)*momentConstant/2)+2)/3
  have hC : 0 ≤ C := by dsimp [C]; positivity [momentConstant_nonneg]
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2*C, ?_⟩
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 3, hlog] with M hM hlogM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlmono : Real.log (M : ℝ) ≤ Real.log (2*(M : ℝ)) :=
    Real.log_le_log hMpos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log (2*(M : ℝ)))]
  calc
    _ ≤ C*(1 + Real.log M) := stationaryAge_main_error hM
    _ ≤ C*(2*Real.log (2*(M : ℝ))) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

theorem firstMoment_isBigO_log :
    Asymptotics.IsBigO atTop
      (fun M : ℕ => firstMoment M - (3/Real.pi^2)*Real.log M^2)
      (fun M : ℕ => Real.log (2*(M : ℝ))) := by
  let C : ℝ := ((7 + Real.pi^2/6)*momentConstant/2)+1
  have hC : 0 ≤ C := by dsimp [C]; positivity [momentConstant_nonneg]
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2*C, ?_⟩
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 3, hlog] with M hM hlogM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlmono : Real.log (M : ℝ) ≤ Real.log (2*(M : ℝ)) :=
    Real.log_le_log hMpos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log (2*(M : ℝ)))]
  calc
    _ ≤ C*(1 + Real.log M) := firstMoment_main_error hM
    _ ≤ C*(2*Real.log (2*(M : ℝ))) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

end NField.Alignment.CollisionStationaryAgeAsymptotic
