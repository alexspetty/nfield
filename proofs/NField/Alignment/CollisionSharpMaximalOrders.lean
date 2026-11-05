/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSharpLimsupTransfer
import NField.Alignment.CollisionResetSharpUpper
import NField.Alignment.CollisionAlignmentSharpUpper

/-!
# Exact global reset and alignment limsups

The actual observables satisfy the sharp upper bounds at every large
integer, and their values on the lcm moduli attain the same constants.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSharpMaximalOrders

open Filter CollisionSharpLimsupTransfer CollisionLcmLogLogScale
open CollisionResetSharpUpper CollisionAlignmentSharpUpper CollisionLimitingPrimeProduct
open CollisionResetIntegrability ProfiniteRemainderMeasure CollisionCylinderMeans
open CollisionOdometerRecurrence

theorem resetFunction_pointwise_nonneg (x : Phase) : 0 ≤ resetFunction x :=
  tsum_nonneg (fun k => resetTerm_nonneg k x)

theorem reset_global_limsup :
    limsup (fun n : ℕ => resetFunction (integerPhase n)/(Real.log (Real.log n))^2) atTop=
      alignmentKappa := by
  apply limsup_eq_of_upper_and_attained (m := cutoffPeriod)
  · exact ⟨0,Filter.Eventually.of_forall (fun n =>
      div_nonneg (resetFunction_pointwise_nonneg _) (sq_nonneg _))⟩
  · exact scaled_upper_to_ratio_upper loglog_square_eventually_pos
      (fun _ hepsilon => integer_reset_sharp_upper hepsilon)
  · exact cutoffPeriod_tendsto_atTop
  · exact lcm_reset_global_ratio_tendsto

theorem alignment_global_limsup :
    limsup (fun L : ℕ => alignmentConstant L/(Real.log (Real.log L))^2) atTop=
      alignmentGamma := by
  apply limsup_eq_of_upper_and_attained (m := cutoffPeriod)
  · refine ⟨0,?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with L hL
    exact div_nonneg (alignmentConstant_nonneg hL) (sq_nonneg _)
  · exact scaled_upper_to_ratio_upper loglog_square_eventually_pos
      (fun _ hepsilon => alignment_sharp_upper hepsilon)
  · exact cutoffPeriod_tendsto_atTop
  · exact lcm_alignment_global_ratio_tendsto

theorem global_reset_and_alignment_limsups :
    limsup (fun n : ℕ => resetFunction (integerPhase n)/(Real.log (Real.log n))^2) atTop=
      alignmentKappa ∧
    limsup (fun L : ℕ => alignmentConstant L/(Real.log (Real.log L))^2) atTop=
      alignmentGamma :=
  ⟨reset_global_limsup,alignment_global_limsup⟩

end NField.Alignment.CollisionSharpMaximalOrders
