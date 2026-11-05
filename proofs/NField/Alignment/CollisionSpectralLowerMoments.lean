/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPositiveLogTail
import NField.Alignment.CollisionSpectralNuBounds

/-!
# Lower-order conductor moment tails

The positive majorant uses the actual logarithmic conductor correction.
The proved second-moment counting bound supplies its linear partial sums.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralLowerMoments

open scoped BigOperators Classical
open Filter
open CollisionConductorArithmetic CollisionSpectralPrimeMoments CollisionSpectralNuBounds
open CollisionPositiveLogTail

def momentMajorant (n : ℕ) : ℝ := if n=0 then 0 else 1+(nu n)^2
def momentMajorantConstant : ℝ := 1+firstPrimeMoment^2+secondPrimeMoment

theorem momentMajorant_zero : momentMajorant 0=0 := by simp [momentMajorant]

theorem momentMajorant_nonneg (n : ℕ) : 0 ≤ momentMajorant n := by
  unfold momentMajorant
  split_ifs <;> positivity

theorem momentMajorantConstant_pos : 0 < momentMajorantConstant := by
  unfold momentMajorantConstant
  positivity [secondPrimeMoment_nonneg]

theorem momentMajorant_partial_bound (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, momentMajorant n) ≤ momentMajorantConstant*N := by
  have he : (∑ n ∈ Finset.Ioc 0 N, momentMajorant n)=
      (N : ℝ)+∑ n ∈ Finset.Ioc 0 N, (nu n)^2 := by
    have he' : (∑ n ∈ Finset.Ioc 0 N, momentMajorant n)=
        ∑ n ∈ Finset.Ioc 0 N, (1+(nu n)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact if_neg (ne_of_gt (Finset.mem_Ioc.mp hn).1)
    rw [he',Finset.sum_add_distrib]
    simp
  rw [he]
  unfold momentMajorantConstant
  nlinarith [nu_second_bound N]

theorem momentMajorant_tail_summable {Q : ℝ} (hQ : 1 ≤ Q) :
    Summable (fun n : ℕ => if Q < (n : ℝ) then positiveLogTerm momentMajorant n else 0) :=
  positiveLog_tail_summable_of_nat momentMajorant_zero momentMajorant_nonneg
    momentMajorantConstant_pos.le hQ momentMajorant_partial_bound

theorem momentMajorant_tail_bound {Q : ℝ} (hQ : 1 ≤ Q) :
    positiveLogTail momentMajorant Q ≤ momentMajorantConstant*(2*Real.log Q+3)/Q :=
  positiveLog_tail_bound_of_nat momentMajorant_zero momentMajorant_nonneg
    momentMajorantConstant_pos.le hQ momentMajorant_partial_bound

theorem momentMajorant_tail_isBigO :
    Asymptotics.IsBigO atTop (positiveLogTail momentMajorant) (fun Q : ℝ => Real.log Q/Q) :=
  positiveLog_tail_isBigO momentMajorant_zero momentMajorant_nonneg
    momentMajorantConstant_pos.le momentMajorant_partial_bound

theorem momentMajorant_tail_isLittleO :
    Asymptotics.IsLittleO atTop (positiveLogTail momentMajorant)
      (fun Q : ℝ => (Real.log Q)^2/Q) :=
  positiveLog_tail_isLittleO momentMajorant_zero momentMajorant_nonneg
    momentMajorantConstant_pos.le momentMajorant_partial_bound

end NField.Alignment.CollisionSpectralLowerMoments
