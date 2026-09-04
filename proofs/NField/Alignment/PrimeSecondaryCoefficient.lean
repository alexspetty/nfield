/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExactSamplingReservoirBridge
import NField.Alignment.SecondaryCapacityLedger

/-!
# Prime secondary-coefficient transfer

The final error transfer is specialized to the actual collision energy,
continuous capacity, and sampling defect.  Nonprime indices are assigned zero
only to make total functions on the naturals; every bound is explicitly
quantified over primes.
-/

namespace NField.Alignment.PrimeSecondaryCoefficient

open Filter Asymptotics
open NField.Alignment.CollisionBernoulliStraightening
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.SecondaryCapacityLedger

/-- The concrete collision energy as a total natural-indexed function. -/
noncomputable def primeCollisionEnergy (p : ℕ) : ℝ :=
  if hp : p.Prime then collisionEnergy hp else 0

/-- The concrete sampling defect as a total natural-indexed function. -/
noncomputable def primeSamplingDefect (p : ℕ) : ℝ :=
  if hp : p.Prime then samplingDefect hp else 0

/-- The continuous main term evaluated at the actual prime-window length. -/
noncomputable def primeContinuousMain (p : ℕ) : ℝ :=
  continuousCapacityMain (p - 1)

/-- The manuscript's continuous `log^(5/3)` remainder at `N = p - 1`. -/
noncomputable def primeContinuousScale (p : ℕ) : ℝ :=
  Real.rpow (Real.log ((p - 1 : ℕ) : ℝ)) (5 / 3 : ℝ)

/-- The strict all-prime sampling scale, including a harmless constant for
the finitely many smallest primes. -/
noncomputable def primeStrictSamplingScale (p : ℕ) : ℝ :=
  1 + Real.log (2 * p) ^ 2 / Real.log (Real.log (3 * p))

/-- The literal error scale printed in the finite secondary-coefficient
corollary, before multiplication by `p²`. -/
noncomputable def primePrintedSamplingScale (p : ℕ) : ℝ :=
  Real.log (2 * p) ^ 2 / Real.log (Real.log (3 * p))

/-- The literal main term displayed in the manuscript's final corollary. -/
noncomputable def primeDisplayedSecondaryMain (p : ℕ) : ℝ :=
  (p : ℝ) ^ 3 - (Real.pi ^ 2)⁻¹ * (p : ℝ) ^ 2 * Real.log p ^ 2

theorem primeContinuousScale_nonneg (p : ℕ) :
    0 ≤ primeContinuousScale p := by
  unfold primeContinuousScale
  apply Real.rpow_nonneg
  by_cases hp : p ≤ 1
  · interval_cases p <;> norm_num
  · have hpredNat : 1 ≤ p - 1 := by omega
    have hpredReal : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredNat
    exact Real.log_nonneg hpredReal

theorem primeStrictSamplingScale_nonneg_of_pos
    {p : ℕ} (hp : 0 < p) :
    0 ≤ primeStrictSamplingScale p := by
  unfold primeStrictSamplingScale
  have hthree : (1 : ℝ) < Real.log (3 * p) := by
    have harg : (Real.exp 1 : ℝ) < 3 * p := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * p := by exact_mod_cast (show 3 ≤ 3 * p by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 3 * p)).2 harg
  have hden : 0 < Real.log (Real.log (3 * p)) := Real.log_pos hthree
  positivity

theorem primeStrictSamplingScale_nonneg_of_prime
    {p : ℕ} (hp : p.Prime) :
    0 ≤ primeStrictSamplingScale p := by
  exact primeStrictSamplingScale_nonneg_of_pos hp.pos

theorem one_le_primeStrictSamplingScale
    {p : ℕ} (hp : 0 < p) :
    1 ≤ primeStrictSamplingScale p := by
  unfold primeStrictSamplingScale
  have hthree : (1 : ℝ) < Real.log (3 * p) := by
    have harg : (Real.exp 1 : ℝ) < 3 * p := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * p := by exact_mod_cast (show 3 ≤ 3 * p by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
  have hden : 0 < Real.log (Real.log (3 * p)) := Real.log_pos hthree
  have hnum : 0 ≤ Real.log (2 * p) ^ 2 := sq_nonneg _
  have : 0 ≤ Real.log (2 * p) ^ 2 / Real.log (Real.log (3 * p)) :=
    div_nonneg hnum hden.le
  linarith

/-- Replacing `p - 1` by `p` in the continuous main term costs at most `p²`. -/
theorem primeContinuousMain_shift_le_square
    {p : ℕ} (hp : 3 ≤ p) :
    |(p : ℝ) ^ 2 * primeContinuousMain p -
        primeDisplayedSecondaryMain p| ≤
      (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by positivity
  have hpredR : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hpredCast : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have hpredDen : (p : ℝ) - 1 ≠ 0 := by nlinarith
  have hlogP0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hlogPred0 : 0 ≤ Real.log ((p - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p - 1 by omega))
  have hlogMono : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hpredR (by exact_mod_cast (Nat.sub_le p 1))
  have hlogP : Real.log (p : ℝ) ≤ (p : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpR
  have hlogPred : Real.log ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
    exact hlogMono.trans hlogP
  have hlogDiff :
      Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
        1 / (((p - 1 : ℕ) : ℝ)) := by
    rw [← Real.log_div hpR.ne' hpredR.ne']
    calc
      Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤
          (p : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hpR hpredR)
      _ = 1 / (((p - 1 : ℕ) : ℝ)) := by
        rw [hpredCast]
        field_simp [hpredDen]
        ring
  have hlogSquareDiffNonneg :
      0 ≤ Real.log (p : ℝ) ^ 2 -
        Real.log ((p - 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hlogSquareDiff :
      Real.log (p : ℝ) ^ 2 -
          Real.log ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
    calc
      Real.log (p : ℝ) ^ 2 -
          Real.log ((p - 1 : ℕ) : ℝ) ^ 2 =
        (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) *
          (Real.log (p : ℝ) + Real.log ((p - 1 : ℕ) : ℝ)) := by ring
      _ ≤ (1 / (((p - 1 : ℕ) : ℝ))) *
          (2 * ((p : ℝ) - 1)) := by
        have hdiff0 : 0 ≤ Real.log (p : ℝ) -
            Real.log ((p - 1 : ℕ) : ℝ) := sub_nonneg.mpr hlogMono
        gcongr
        linarith
      _ = 2 := by
        rw [hpredCast]
        field_simp [hpredDen]
  have hpiInv0 : 0 ≤ (Real.pi ^ 2)⁻¹ := by positivity
  have hpiInv1 : (Real.pi ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    nlinarith [Real.pi_gt_three]
  have hinside :
      |-1 + (Real.pi ^ 2)⁻¹ *
          (Real.log (p : ℝ) ^ 2 -
            Real.log ((p - 1 : ℕ) : ℝ) ^ 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  unfold primeContinuousMain continuousCapacityMain
  unfold primeDisplayedSecondaryMain
  rw [show
      (p : ℝ) ^ 2 *
          (((p - 1 : ℕ) : ℝ) -
            (Real.pi ^ 2)⁻¹ *
              Real.log ((p - 1 : ℕ) : ℝ) ^ 2) -
          ((p : ℝ) ^ 3 -
            (Real.pi ^ 2)⁻¹ * (p : ℝ) ^ 2 * Real.log p ^ 2) =
        (p : ℝ) ^ 2 *
          (-1 + (Real.pi ^ 2)⁻¹ *
            (Real.log p ^ 2 -
              Real.log ((p - 1 : ℕ) : ℝ) ^ 2)) by
    rw [hpredCast]
    ring]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
  simpa using mul_le_mul_of_nonneg_left hinside (sq_nonneg (p : ℝ))

/-- The same shift is absorbed by one copy of the strict sampling scale. -/
theorem primeContinuousMain_shift_le
    {p : ℕ} (hp : 3 ≤ p) :
    |(p : ℝ) ^ 2 * primeContinuousMain p -
        primeDisplayedSecondaryMain p| ≤
      (p : ℝ) ^ 2 * primeStrictSamplingScale p := by
  calc
    _ ≤ (p : ℝ) ^ 2 := primeContinuousMain_shift_le_square hp
    _ ≤ (p : ℝ) ^ 2 * primeStrictSamplingScale p := by
      have hscale := one_le_primeStrictSamplingScale (by omega : 0 < p)
      simpa using mul_le_mul_of_nonneg_left hscale (sq_nonneg (p : ℝ))

/-- The continuous `log^(5/3)` remainder is eventually dominated by the
strict carrier-sampling scale printed in the manuscript. -/
theorem primeContinuousScale_le_strict_eventually :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ,
      ∀ p, threshold ≤ p →
        primeContinuousScale p ≤ C * primeStrictSamplingScale p := by
  have hloglog :
      (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        (fun x : ℝ => (Real.log x) ^ (1 / 3 : ℝ)) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
          Real.tendsto_log_atTop
  have hthreeTendsto :
      Filter.Tendsto (fun x : ℝ => 3 * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hscaled :
      (fun x : ℝ => Real.log (Real.log (3 * x))) =o[atTop]
        (fun x : ℝ => (Real.log (3 * x)) ^ (1 / 3 : ℝ)) := by
    simpa [Function.comp_def] using hloglog.comp_tendsto hthreeTendsto
  have hnat := hscaled.natCast_atTop.bound (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hnat
  rcases hnat with ⟨N₀, hN₀⟩
  refine ⟨4, by norm_num, max N₀ 3, ?_⟩
  intro p hp
  have hpN : N₀ ≤ p := (le_max_left _ _).trans hp
  have hp3 : 3 ≤ p := (le_max_right N₀ 3).trans hp
  have hpR : (0 : ℝ) < p := by positivity
  have hpredR : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hlogP0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hlogPpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogPred0 : 0 ≤ Real.log ((p - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p - 1 by omega))
  have hlog2P0 : 0 ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by omega))
  have hlog3P0 : 0 ≤ Real.log (3 * (p : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * p by omega))
  have hloglog3P : 0 < Real.log (Real.log (3 * (p : ℝ))) := by
    have harg : Real.exp 1 < 3 * (p : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * p := by exact_mod_cast (show 3 ≤ 3 * p by omega)
    exact Real.log_pos ((Real.lt_log_iff_exp_lt (by positivity)).2 harg)
  have hlittle := hN₀ p hpN
  have hdenBound : Real.log (Real.log (3 * (p : ℝ))) ≤
      (Real.log (3 * (p : ℝ))) ^ (1 / 3 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_pos hloglog3P,
      abs_of_nonneg (Real.rpow_nonneg hlog3P0 _)] using hlittle
  have hlog3le : Real.log (3 * (p : ℝ)) ≤ 2 * Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hpR.ne']
    have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by exact_mod_cast hp3 : (3 : ℝ) ≤ p)
    linarith
  have hrpow3le : (Real.log (3 * (p : ℝ))) ^ (1 / 3 : ℝ) ≤
      2 * (Real.log (p : ℝ)) ^ (1 / 3 : ℝ) := by
    calc
      (Real.log (3 * (p : ℝ))) ^ (1 / 3 : ℝ) ≤
          (2 * Real.log (p : ℝ)) ^ (1 / 3 : ℝ) := by
        exact Real.rpow_le_rpow hlog3P0 hlog3le (by norm_num)
      _ = (2 : ℝ) ^ (1 / 3 : ℝ) *
          (Real.log (p : ℝ)) ^ (1 / 3 : ℝ) := by
        exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlogP0
      _ ≤ 2 * (Real.log (p : ℝ)) ^ (1 / 3 : ℝ) := by
        have htwo : Real.rpow 2 (1 / 3 : ℝ) ≤ Real.rpow 2 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        exact mul_le_mul_of_nonneg_right (by simpa using htwo)
          (Real.rpow_nonneg hlogP0 _)
  have hpredle : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hpredR (by exact_mod_cast (Nat.sub_le p 1))
  have hcontle : primeContinuousScale p ≤
      (Real.log (p : ℝ)) ^ (5 / 3 : ℝ) := by
    unfold primeContinuousScale
    exact Real.rpow_le_rpow hlogPred0 hpredle (by norm_num)
  have hproduct : primeContinuousScale p *
      Real.log (Real.log (3 * (p : ℝ))) ≤
      2 * Real.log (p : ℝ) ^ 2 := by
    calc
      primeContinuousScale p * Real.log (Real.log (3 * (p : ℝ))) ≤
          (Real.log (p : ℝ)) ^ (5 / 3 : ℝ) *
            (2 * (Real.log (p : ℝ)) ^ (1 / 3 : ℝ)) :=
        mul_le_mul hcontle (hdenBound.trans hrpow3le)
          (by positivity) (by positivity)
      _ = 2 * Real.log (p : ℝ) ^ 2 := by
        calc
          _ = 2 * ((Real.log (p : ℝ)) ^ (5 / 3 : ℝ) *
              (Real.log (p : ℝ)) ^ (1 / 3 : ℝ)) := by ring
          _ = 2 * (Real.log (p : ℝ)) ^ ((5 / 3 : ℝ) + 1 / 3) := by
            rw [Real.rpow_add hlogPpos]
          _ = 2 * Real.log (p : ℝ) ^ 2 := by norm_num
  have hlogP2le : Real.log (p : ℝ) ^ 2 ≤
      Real.log (2 * (p : ℝ)) ^ 2 := by
    have hmono : Real.log (p : ℝ) ≤ Real.log (2 * (p : ℝ)) :=
      Real.log_le_log hpR (by nlinarith)
    nlinarith
  have hratio : primeContinuousScale p ≤
      2 * (Real.log (2 * (p : ℝ)) ^ 2 /
        Real.log (Real.log (3 * (p : ℝ)))) := by
    rw [show 2 * (Real.log (2 * (p : ℝ)) ^ 2 /
        Real.log (Real.log (3 * (p : ℝ)))) =
      (2 * Real.log (2 * (p : ℝ)) ^ 2) /
        Real.log (Real.log (3 * (p : ℝ))) by ring]
    apply (le_div_iff₀ hloglog3P).2
    exact hproduct.trans (by gcongr)
  unfold primeStrictSamplingScale
  have hratio0 : 0 ≤ Real.log (2 * (p : ℝ)) ^ 2 /
      Real.log (Real.log (3 * (p : ℝ))) := by positivity
  linarith

/-- The harmless additive constant in the strict scale is absorbed by the
literal positive logarithmic quotient. -/
theorem primeStrictSamplingScale_le_printed
    {p : ℕ} (hp : 3 ≤ p) :
    primeStrictSamplingScale p ≤ 3 * primePrintedSamplingScale p := by
  have hpR : (0 : ℝ) < p := by positivity
  have hlogP : (1 : ℝ) ≤ Real.log (p : ℝ) := by
    exact (show (1 : ℝ) ≤ Real.log 3 from Real.log_three_gt_d9.le.trans'
      (by norm_num)).trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hp))
  have hlog2P : Real.log (p : ℝ) ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_le_log hpR (by nlinarith)
  have hlog3P : Real.log (3 * (p : ℝ)) ≤ 2 * Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hpR.ne']
    have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by exact_mod_cast hp : (3 : ℝ) ≤ p)
    linarith
  have hlog3Ppos : 0 < Real.log (3 * (p : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 3 * p by omega))
  have hden : 0 < Real.log (Real.log (3 * (p : ℝ))) := by
    have harg : Real.exp 1 < 3 * (p : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * p := by exact_mod_cast (show 3 ≤ 3 * p by omega)
    exact Real.log_pos ((Real.lt_log_iff_exp_lt (by positivity)).2 harg)
  have hdenLe : Real.log (Real.log (3 * (p : ℝ))) ≤
      2 * Real.log (2 * (p : ℝ)) ^ 2 := by
    have hbasic := Real.log_le_sub_one_of_pos hlog3Ppos
    have hlog2One : 1 ≤ Real.log (2 * (p : ℝ)) := hlogP.trans hlog2P
    nlinarith [sq_nonneg (Real.log (2 * (p : ℝ)) - 1)]
  have hhalf : (1 / 2 : ℝ) ≤ primePrintedSamplingScale p := by
    unfold primePrintedSamplingScale
    apply (le_div_iff₀ hden).2
    nlinarith
  unfold primeStrictSamplingScale
  unfold primePrintedSamplingScale at hhalf ⊢
  nlinarith

/-- The combined finite-transfer scale is eventually bounded by the exact
single scale printed in the manuscript. -/
theorem primeCombinedScale_le_printed_eventually :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ,
      ∀ p, threshold ≤ p →
        (p : ℝ) ^ 2 *
            (primeContinuousScale p + primeStrictSamplingScale p) ≤
          C * ((p : ℝ) ^ 2 * primePrintedSamplingScale p) := by
  rcases primeContinuousScale_le_strict_eventually with
    ⟨C, hC, N₀, hcontinuous⟩
  refine ⟨3 * (C + 1), by positivity, max N₀ 3, ?_⟩
  intro p hp
  have hpN : N₀ ≤ p := (le_max_left _ _).trans hp
  have hp3 : 3 ≤ p := (le_max_right N₀ 3).trans hp
  have hstrict0 := primeStrictSamplingScale_nonneg_of_pos (by omega : 0 < p)
  have hprinted0 : 0 ≤ primePrintedSamplingScale p := by
    unfold primePrintedSamplingScale
    have hden : 0 < Real.log (Real.log (3 * (p : ℝ))) := by
      have harg : Real.exp 1 < 3 * (p : ℝ) := by
        calc
          Real.exp 1 < 3 := Real.exp_one_lt_three
          _ ≤ 3 * p := by exact_mod_cast (show 3 ≤ 3 * p by omega)
      exact Real.log_pos ((Real.lt_log_iff_exp_lt (by positivity)).2 harg)
    positivity
  have hsum : primeContinuousScale p + primeStrictSamplingScale p ≤
      (C + 1) * primeStrictSamplingScale p := by
    calc
      _ ≤ C * primeStrictSamplingScale p +
          primeStrictSamplingScale p :=
        add_le_add (hcontinuous p hpN) le_rfl
      _ = _ := by ring
  have hstrict := primeStrictSamplingScale_le_printed hp3
  calc
    (p : ℝ) ^ 2 *
        (primeContinuousScale p + primeStrictSamplingScale p) ≤
      (p : ℝ) ^ 2 * ((C + 1) * primeStrictSamplingScale p) := by
        gcongr
    _ ≤ (p : ℝ) ^ 2 *
        ((C + 1) * (3 * primePrintedSamplingScale p)) := by
      gcongr
    _ = 3 * (C + 1) *
        ((p : ℝ) ^ 2 * primePrintedSamplingScale p) := by ring

/-- An eventual error bound restricted to prime indices. -/
def PrimeEventualErrorBound
    (value main scale : ℕ → ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧ ∃ threshold : ℕ,
    ∀ p, threshold ≤ p → p.Prime →
      |value p - main p| ≤ constant * scale p

/-- The exact finite decomposition on every prime index. -/
theorem prime_secondary_split {p : ℕ} (hp : p.Prime) :
    primeCollisionEnergy p =
      (p : ℝ) ^ 2 *
        (continuousCapacity (p - 1) - primeSamplingDefect p) := by
  rw [primeCollisionEnergy, dif_pos hp,
    primeSamplingDefect, dif_pos hp]
  unfold samplingDefect
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hpR]
  ring

/-- The actual finite secondary coefficient inherits the continuous and
sampling envelopes through the exact prime-square split. -/
theorem finite_secondary_coefficient
    (mainCapacity continuousScale samplingScale : ℕ → ℝ)
    (hcapacity : PrimeEventualErrorBound
      (fun p => continuousCapacity (p - 1)) mainCapacity continuousScale)
    (hsampling : PrimeEventualErrorBound
      primeSamplingDefect (fun _ => 0) samplingScale)
    (hcontinuousScale : ∀ p, 0 ≤ continuousScale p)
    (hsamplingScale : ∀ p, 0 ≤ samplingScale p) :
    PrimeEventualErrorBound primeCollisionEnergy
      (fun p => (p : ℝ) ^ 2 * mainCapacity p)
      (fun p => (p : ℝ) ^ 2 *
        (continuousScale p + samplingScale p)) := by
  rcases hcapacity with ⟨C₁, hC₁, N₁, hcapacity⟩
  rcases hsampling with ⟨C₂, hC₂, N₂, hsampling⟩
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁,
    max N₁ N₂, ?_⟩
  intro p hpN hp
  have hp₁ : N₁ ≤ p := (le_max_left _ _).trans hpN
  have hp₂ : N₂ ≤ p := (le_max_right _ _).trans hpN
  have hcap := hcapacity p hp₁ hp
  have hsamp := hsampling p hp₂ hp
  simp only [sub_zero] at hsamp
  rw [prime_secondary_split hp]
  rw [show (p : ℝ) ^ 2 *
        (continuousCapacity (p - 1) - primeSamplingDefect p) -
        (p : ℝ) ^ 2 * mainCapacity p =
      (p : ℝ) ^ 2 *
        ((continuousCapacity (p - 1) - mainCapacity p) -
          primeSamplingDefect p) by ring]
  rw [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg p)]
  have hp2nonneg : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
  calc
    (p : ℝ) ^ 2 *
        |(continuousCapacity (p - 1) - mainCapacity p) -
          primeSamplingDefect p| ≤
      (p : ℝ) ^ 2 *
        (|continuousCapacity (p - 1) - mainCapacity p| +
          |primeSamplingDefect p|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ (p : ℝ) ^ 2 *
        (C₁ * continuousScale p + C₂ * samplingScale p) := by
      gcongr
    _ ≤ max C₁ C₂ *
        ((p : ℝ) ^ 2 *
          (continuousScale p + samplingScale p)) := by
      have hmax₁ : C₁ ≤ max C₁ C₂ := le_max_left _ _
      have hmax₂ : C₂ ≤ max C₁ C₂ := le_max_right _ _
      have hc := hcontinuousScale p
      have hs := hsamplingScale p
      calc
        (p : ℝ) ^ 2 *
            (C₁ * continuousScale p + C₂ * samplingScale p) ≤
          (p : ℝ) ^ 2 *
            (max C₁ C₂ * continuousScale p +
              max C₁ C₂ * samplingScale p) := by
            apply mul_le_mul_of_nonneg_left _ hp2nonneg
            exact add_le_add
              (mul_le_mul_of_nonneg_right hmax₁ hc)
              (mul_le_mul_of_nonneg_right hmax₂ hs)
        _ = max C₁ C₂ *
            ((p : ℝ) ^ 2 *
              (continuousScale p + samplingScale p)) := by ring

/-- The finite coefficient transfer specialized to the manuscript's actual
continuous and strict-sampling scales. -/
theorem finite_secondary_coefficient_actual
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ)))
    (hsampling : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * primeStrictSamplingScale p) :
    PrimeEventualErrorBound primeCollisionEnergy
      (fun p => (p : ℝ) ^ 2 * primeContinuousMain p)
      (fun p => (p : ℝ) ^ 2 *
        (primeContinuousScale p + primeStrictSamplingScale p)) := by
  have hcapacityPrime : PrimeEventualErrorBound
      (fun p => continuousCapacity (p - 1)) primeContinuousMain
      primeContinuousScale := by
    rcases hcapacity with ⟨C, hC, N₀, hbound⟩
    refine ⟨C, hC, N₀ + 1, ?_⟩
    intro p hpN _hp
    have hpred : N₀ ≤ p - 1 := by omega
    unfold primeContinuousMain primeContinuousScale
    exact hbound (p - 1) hpred
  have hsamplingPrime : PrimeEventualErrorBound primeSamplingDefect
      (fun _ => 0) primeStrictSamplingScale := by
    rcases hsampling with ⟨C, hC, hbound⟩
    refine ⟨C, hC, 0, ?_⟩
    intro p _ hp
    simpa using hbound p hp
  exact finite_secondary_coefficient primeContinuousMain
    primeContinuousScale primeStrictSamplingScale hcapacityPrime hsamplingPrime
    primeContinuousScale_nonneg
    (fun p => by
      by_cases hp0 : p = 0
      · simp [hp0, primeStrictSamplingScale]
      · exact primeStrictSamplingScale_nonneg_of_pos
          (Nat.pos_of_ne_zero hp0))

/-- The final coefficient transfer with the manuscript's literal displayed
main term.  The only remaining simplification is domination of the continuous
`log^(5/3)` scale by the printed strict sampling scale. -/
theorem finite_secondary_coefficient_displayed_main
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ)))
    (hsampling : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * primeStrictSamplingScale p) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 *
        (primeContinuousScale p + primeStrictSamplingScale p)) := by
  rcases finite_secondary_coefficient_actual hcapacity hsampling with
    ⟨C, hC, N₀, hbound⟩
  refine ⟨C + 1, by positivity, max N₀ 3, ?_⟩
  intro p hpN hpPrime
  have hpN₀ : N₀ ≤ p := (le_max_left _ _).trans hpN
  have hp3 : 3 ≤ p := (le_max_right N₀ 3).trans hpN
  have hbase := hbound p hpN₀ hpPrime
  have hshift := primeContinuousMain_shift_le hp3
  have hcontinuous0 := primeContinuousScale_nonneg p
  have hstrict0 := primeStrictSamplingScale_nonneg_of_prime hpPrime
  have hp20 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
  calc
    |primeCollisionEnergy p - primeDisplayedSecondaryMain p| ≤
        |primeCollisionEnergy p -
          (p : ℝ) ^ 2 * primeContinuousMain p| +
        |(p : ℝ) ^ 2 * primeContinuousMain p -
          primeDisplayedSecondaryMain p| := by
      exact abs_sub_le _ _ _
    _ ≤ C * ((p : ℝ) ^ 2 *
          (primeContinuousScale p + primeStrictSamplingScale p)) +
        (p : ℝ) ^ 2 * primeStrictSamplingScale p :=
      add_le_add hbase hshift
    _ ≤ C * ((p : ℝ) ^ 2 *
          (primeContinuousScale p + primeStrictSamplingScale p)) +
        (p : ℝ) ^ 2 *
          (primeContinuousScale p + primeStrictSamplingScale p) := by
      have : primeStrictSamplingScale p ≤
          primeContinuousScale p + primeStrictSamplingScale p := by
        linarith
      gcongr
    _ = (C + 1) * ((p : ℝ) ^ 2 *
          (primeContinuousScale p + primeStrictSamplingScale p)) := by ring

/-- The manuscript's final corollary with both its literal main term and its
literal single error scale. -/
theorem finite_secondary_coefficient_printed
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ)))
    (hsampling : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * primeStrictSamplingScale p) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) := by
  rcases finite_secondary_coefficient_displayed_main hcapacity hsampling with
    ⟨C, hC, N₁, hbound⟩
  rcases primeCombinedScale_le_printed_eventually with
    ⟨D, hD, N₂, hscale⟩
  refine ⟨C * D, mul_nonneg hC hD, max N₁ N₂, ?_⟩
  intro p hpN hpPrime
  have hpN₁ : N₁ ≤ p := (le_max_left _ _).trans hpN
  have hpN₂ : N₂ ≤ p := (le_max_right _ _).trans hpN
  calc
    |primeCollisionEnergy p - primeDisplayedSecondaryMain p| ≤
        C * ((p : ℝ) ^ 2 *
          (primeContinuousScale p + primeStrictSamplingScale p)) :=
      hbound p hpN₁ hpPrime
    _ ≤ C * (D * ((p : ℝ) ^ 2 * primePrintedSamplingScale p)) := by
      exact mul_le_mul_of_nonneg_left (hscale p hpN₂) hC
    _ = C * D * ((p : ℝ) ^ 2 * primePrintedSamplingScale p) := by ring

/-- Under logarithmic sampling damping, the manuscript's existing continuous
remainder becomes the sole error scale. -/
theorem finite_secondary_coefficient_under_log_sampling
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ)))
    (hsampling : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * Real.log p) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primeContinuousScale p) := by
  have hcapacityPrime : PrimeEventualErrorBound
      (fun p => continuousCapacity (p - 1)) primeContinuousMain
      primeContinuousScale := by
    rcases hcapacity with ⟨C, hC, N₀, hbound⟩
    refine ⟨C, hC, N₀ + 1, ?_⟩
    intro p hpN _hp
    exact hbound (p - 1) (by omega)
  have hsamplingPrime : PrimeEventualErrorBound primeSamplingDefect
      (fun _ => 0) primeContinuousScale := by
    rcases hsampling with ⟨C, hC, hbound⟩
    refine ⟨2 * C, by positivity, 4, ?_⟩
    intro p hp4 hpPrime
    have hpredR : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < p - 1 by omega)
    have hlogPredOne : (1 : ℝ) ≤ Real.log ((p - 1 : ℕ) : ℝ) := by
      have hthree : (1 : ℝ) ≤ Real.log 3 :=
        le_trans (by norm_num) Real.log_three_gt_d9.le
      exact hthree.trans
        (Real.log_le_log (by norm_num)
          (by exact_mod_cast (show 3 ≤ p - 1 by omega)))
    have hpSquare : p ≤ (p - 1) ^ 2 := by
      calc
        p = (p - 1) + 1 := by omega
        _ ≤ 2 * (p - 1) := by omega
        _ ≤ (p - 1) * (p - 1) :=
          Nat.mul_le_mul_right (p - 1) (by omega : 2 ≤ p - 1)
        _ = (p - 1) ^ 2 := by ring
    have hlogP : Real.log (p : ℝ) ≤
        2 * Real.log ((p - 1 : ℕ) : ℝ) := by
      have hmono := Real.log_le_log (by positivity : (0 : ℝ) < p)
        (by exact_mod_cast hpSquare : (p : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2)
      rw [Real.log_pow] at hmono
      norm_num at hmono
      exact hmono
    have hpredScale : Real.log ((p - 1 : ℕ) : ℝ) ≤
        primeContinuousScale p := by
      unfold primeContinuousScale
      exact Real.self_le_rpow_of_one_le hlogPredOne (by norm_num)
    have hs := hbound p hpPrime
    simp only [sub_zero]
    calc
      |primeSamplingDefect p| ≤ C * Real.log p := hs
      _ ≤ C * (2 * primeContinuousScale p) := by
        gcongr
        exact hlogP.trans (by linarith)
      _ = (2 * C) * primeContinuousScale p := by ring
  have hbase := finite_secondary_coefficient primeContinuousMain
    primeContinuousScale primeContinuousScale hcapacityPrime hsamplingPrime
    primeContinuousScale_nonneg primeContinuousScale_nonneg
  rcases hbase with ⟨C, hC, N₀, hbound⟩
  refine ⟨2 * C + 1, by positivity, max N₀ 4, ?_⟩
  intro p hpN hpPrime
  have hpN₀ : N₀ ≤ p := (le_max_left _ _).trans hpN
  have hp4 : 4 ≤ p := (le_max_right N₀ 4).trans hpN
  have hscaleOne : (1 : ℝ) ≤ primeContinuousScale p := by
    unfold primeContinuousScale
    have hlogOne : (1 : ℝ) ≤ Real.log ((p - 1 : ℕ) : ℝ) := by
      have hthree : (1 : ℝ) ≤ Real.log 3 :=
        le_trans (by norm_num) Real.log_three_gt_d9.le
      exact hthree.trans
        (Real.log_le_log (by norm_num)
          (by exact_mod_cast (show 3 ≤ p - 1 by omega)))
    exact Real.one_le_rpow hlogOne (by norm_num)
  have hshift := primeContinuousMain_shift_le_square (by omega : 3 ≤ p)
  calc
    |primeCollisionEnergy p - primeDisplayedSecondaryMain p| ≤
        |primeCollisionEnergy p -
          (p : ℝ) ^ 2 * primeContinuousMain p| +
        |(p : ℝ) ^ 2 * primeContinuousMain p -
          primeDisplayedSecondaryMain p| := abs_sub_le _ _ _
    _ ≤ C * ((p : ℝ) ^ 2 *
          (primeContinuousScale p + primeContinuousScale p)) +
        (p : ℝ) ^ 2 := add_le_add (hbound p hpN₀ hpPrime) hshift
    _ ≤ (2 * C + 1) * ((p : ℝ) ^ 2 * primeContinuousScale p) := by
      have hp20 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
      nlinarith

/-- If continuous capacity is separately sharpened to a logarithmic
remainder, logarithmic sampling gives the paper's `p² log p` error. -/
theorem finite_secondary_coefficient_under_log_capacity_and_sampling
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.log N))
    (hsampling : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * Real.log p) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * Real.log p) := by
  have hcapacityPrime : PrimeEventualErrorBound
      (fun p => continuousCapacity (p - 1)) primeContinuousMain
      (fun p => Real.log p) := by
    rcases hcapacity with ⟨C, hC, N₀, hbound⟩
    refine ⟨C, hC, N₀ + 1, ?_⟩
    intro p hpN hpPrime
    have hp2 := hpPrime.two_le
    have hpPred : N₀ ≤ p - 1 := by omega
    have hpred := hbound (p - 1) hpPred
    have hlogMono : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < p - 1 by omega))
        (by exact_mod_cast (Nat.sub_le p 1))
    exact hpred.trans (mul_le_mul_of_nonneg_left hlogMono hC)
  have hsamplingPrime : PrimeEventualErrorBound primeSamplingDefect
      (fun _ => 0) (fun p => Real.log p) := by
    rcases hsampling with ⟨C, hC, hbound⟩
    exact ⟨C, hC, 0, fun p _ hp => by simpa using hbound p hp⟩
  have hbase := finite_secondary_coefficient primeContinuousMain
    (fun p => Real.log p) (fun p => Real.log p)
    hcapacityPrime hsamplingPrime
    (fun p => by
      by_cases hp0 : p = 0
      · simp [hp0]
      · exact Real.log_nonneg
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp0)))
    (fun p => by
      by_cases hp0 : p = 0
      · simp [hp0]
      · exact Real.log_nonneg
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp0)))
  rcases hbase with ⟨C, hC, N₀, hbound⟩
  refine ⟨2 * C + 1, by positivity, max N₀ 3, ?_⟩
  intro p hpN hpPrime
  have hpN₀ : N₀ ≤ p := (le_max_left _ _).trans hpN
  have hp3 : 3 ≤ p := (le_max_right N₀ 3).trans hpN
  have hlogOne : (1 : ℝ) ≤ Real.log (p : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 :=
      le_trans (by norm_num) Real.log_three_gt_d9.le
    exact hthree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hp3))
  have hshift := primeContinuousMain_shift_le_square hp3
  calc
    |primeCollisionEnergy p - primeDisplayedSecondaryMain p| ≤
        |primeCollisionEnergy p -
          (p : ℝ) ^ 2 * primeContinuousMain p| +
        |(p : ℝ) ^ 2 * primeContinuousMain p -
          primeDisplayedSecondaryMain p| := abs_sub_le _ _ _
    _ ≤ C * ((p : ℝ) ^ 2 * (Real.log p + Real.log p)) +
        (p : ℝ) ^ 2 := add_le_add (hbound p hpN₀ hpPrime) hshift
    _ ≤ (2 * C + 1) * ((p : ℝ) ^ 2 * Real.log p) := by
      have hp20 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
      nlinarith

end NField.Alignment.PrimeSecondaryCoefficient
