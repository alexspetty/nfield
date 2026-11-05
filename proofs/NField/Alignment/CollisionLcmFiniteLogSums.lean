/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmFiniteProducts

/-!
# The logarithmic lcm sums with their actual finite exponents

The uniform local-loss estimate is lower order than log(m). It transfers
the proved limiting-prime asymptotic to each actual finite logarithmic sum.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmFiniteLogSums

open scoped Classical
open Filter Asymptotics CollisionLcmFiniteProducts CollisionLcmFactorErrors
open CollisionMertensInput CollisionLimitingPrimeLogSum CollisionResetEulerProduct
open CollisionOdometerRecurrence

theorem sqrt_log_loss_isLittleO (f : ℕ → ℝ) (hf0 : ∀ m, 0 ≤ f m)
    (hf : ∀ m, 4 ≤ m → f m ≤ 9*Real.log m/Real.sqrt m) :
    f =o[atTop] (fun m : ℕ => Real.log m) := by
  apply isLittleO_iff.mpr
  intro c hc
  have hsmall : ∀ᶠ m : ℕ in atTop, 9/Real.sqrt m < c :=
    (inverse_sqrt_nat_tendsto 9).eventually_lt_const hc
  filter_upwards [eventually_ge_atTop (4 : ℕ),hsmall] with m hm hmc
  rw [Real.norm_of_nonneg (hf0 m),Real.norm_of_nonneg (Real.log_natCast_nonneg m)]
  calc
    _ ≤ 9*Real.log m/Real.sqrt m := hf m hm
    _ = (9/Real.sqrt m)*Real.log m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmc.le (Real.log_natCast_nonneg m)

theorem lcmAlignmentAverageLoss_isLittleO :
    lcmAlignmentAverageLoss =o[atTop] (fun m : ℕ => Real.log m) :=
  sqrt_log_loss_isLittleO _ lcmAlignmentAverageLoss_nonneg
    (fun _ hm => lcmAlignmentAverageLoss_bound hm)

theorem lcmResetAverageLoss_isLittleO :
    lcmResetAverageLoss =o[atTop] (fun m : ℕ => Real.log m) :=
  sqrt_log_loss_isLittleO _ lcmResetAverageLoss_nonneg
    (fun _ hm => lcmResetAverageLoss_bound hm)

theorem lcmAlignmentFiniteLogSum_loss_identity (m : ℕ) :
    lcmAlignmentFiniteLogSum m=limitingPrimeLogSum m-lcmAlignmentAverageLoss m := by
  unfold limitingPrimeLogSum lcmAlignmentAverageLoss lcmAlignmentFiniteLogSum
  rw [primesUpTo_natCast,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem lcmResetEulerLogSum_loss_identity (m : ℕ) :
    resetEulerLogSum (cutoffPeriod m)=limitingPrimeLogSum m-lcmResetAverageLoss m := by
  rw [lcmResetEulerLogSum_formula]
  unfold limitingPrimeLogSum lcmResetAverageLoss
  rw [primesUpTo_natCast,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem lcmAlignmentFiniteLogSum_asymptotic :
    lcmAlignmentFiniteLogSum ~[atTop] (fun m : ℕ => Real.log m) := by
  have h := (limitingPrimeLogSum_asymptotic.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).sub_isLittleO lcmAlignmentAverageLoss_isLittleO
  convert! h using 1
  funext m
  exact lcmAlignmentFiniteLogSum_loss_identity m

theorem lcmResetEulerLogSum_asymptotic :
    (fun m : ℕ => resetEulerLogSum (cutoffPeriod m)) ~[atTop] (fun m : ℕ => Real.log m) := by
  have h := (limitingPrimeLogSum_asymptotic.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).sub_isLittleO lcmResetAverageLoss_isLittleO
  convert! h using 1
  funext m
  exact lcmResetEulerLogSum_loss_identity m

end NField.Alignment.CollisionLcmFiniteLogSums
