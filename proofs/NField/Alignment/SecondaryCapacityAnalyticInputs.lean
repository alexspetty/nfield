/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.GcdLcmCapacity
import NField.Alignment.ReducedHarmonicMobius
import NField.Alignment.WeightedFractionalPartTransfer
import NField.Alignment.FractionalMobiusAsymptotic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Analytic inputs for the continuous secondary capacity

The paper uses one published weighted fractional-part theorem and elementary
tail/Möbius transfer estimates.  Their statements are fixed here on the
actual finite functions and the manuscript's `log^(5/3)` remainder scale.
-/

namespace NField.Alignment.SecondaryCapacityAnalyticInputs

open NField.Alignment.ReducedHarmonicMobius
open NField.Alignment.GcdLcmCapacity
open NField.Alignment.SecondaryCapacityLedger
open NField.Alignment.CoprimeEulerMass
open NField.Alignment.WeightedFractionalPartTransfer
open NField.Alignment.FractionalMobiusAsymptotic

/-- The manuscript's fixed continuous remainder scale. -/
noncomputable def secondaryCapacityRemainderScale (N : ℕ) : ℝ :=
  Real.rpow (Real.log N) (5 / 3 : ℝ)

theorem secondaryCapacityRemainderScale_nonneg (N : ℕ) :
    0 ≤ secondaryCapacityRemainderScale N := by
  unfold secondaryCapacityRemainderScale
  apply Real.rpow_nonneg
  by_cases hN : N = 0
  · simp [hN]
  · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN))

/-- Consequence of the Saffari--Vaughan weighted fractional-part theorem on
the actual `W(N)` used by the Möbius reduction. -/
def WeightedFractionalPartsEstimate : Prop :=
  EventualErrorBound
    (fun N => weightedFractionalPartsAtQuotient N 1)
    (fun N => (1 / 4 : ℝ) * Real.log N ^ 2)
    secondaryCapacityRemainderScale

/-- The elementary Euler-tail contribution is below the same scale. -/
def ReducedEulerTailEstimate : Prop :=
  EventualErrorBound
    (fun N => (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N)
    (fun _ => 0) secondaryCapacityRemainderScale

/-- The reduced Euler tail needs no analytic certificate.  The exact
Calkin--Wilf telescoping formula identifies it with a positive frontier, whose
explicit harmonic bound is smaller than the manuscript's remainder scale. -/
theorem reduced_euler_tail_estimate : ReducedEulerTailEstimate := by
  refine ⟨6, by norm_num, 3, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by positivity
  have htail := reducedEulerTailMass_eq_frontier hN2
  have hfrontNonneg := eulerFrontierPotential_nonneg N
  have hvalueNonneg :
      0 ≤ (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N := by
    rw [htail]
    positivity
  simp only [sub_zero]
  rw [abs_of_nonneg hvalueNonneg, htail]
  have hfront := eulerFrontierPotential_le hN2
  have hmul := mul_le_mul_of_nonneg_left hfront
    (show 0 ≤ (2 / 3 : ℝ) * (N : ℝ) by positivity)
  have hprimary :
      (2 / 3 : ℝ) * (N : ℝ) * eulerFrontierPotential N ≤
        4 + (4 / 3 : ℝ) * Real.log N := by
    calc
      (2 / 3 : ℝ) * (N : ℝ) * eulerFrontierPotential N ≤
          (2 / 3 : ℝ) * (N : ℝ) *
            (4 / (N : ℝ) +
              2 * (harmonic N : ℝ) / (N : ℝ)) := hmul
      _ = (8 / 3 : ℝ) + (4 / 3 : ℝ) * (harmonic N : ℝ) := by
        field_simp [ne_of_gt hNR]
        ring
      _ ≤ 4 + (4 / 3 : ℝ) * Real.log N := by
        have hharmonic := harmonic_le_one_add_log N
        norm_num at hharmonic ⊢
        linarith
  have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
    exact le_trans (by norm_num) Real.log_three_gt_d9.le
  have hlog : (1 : ℝ) ≤ Real.log N := by
    exact hlogThree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hscaleOne : (1 : ℝ) ≤ secondaryCapacityRemainderScale N := by
    unfold secondaryCapacityRemainderScale
    exact Real.one_le_rpow hlog (by norm_num)
  have hlogScale : Real.log N ≤ secondaryCapacityRemainderScale N := by
    unfold secondaryCapacityRemainderScale
    exact Real.self_le_rpow_of_one_le hlog (by norm_num)
  have hscaleNonneg := secondaryCapacityRemainderScale_nonneg N
  calc
    (2 / 3 : ℝ) * (N : ℝ) * eulerFrontierPotential N ≤
        4 + (4 / 3 : ℝ) * Real.log N := hprimary
    _ ≤ 6 * secondaryCapacityRemainderScale N := by nlinarith

theorem weighted_fractional_parts
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    WeightedFractionalPartsEstimate :=
  weighted_fractional_parts_of_saffari_vaughan hSaffariVaughan

theorem fractional_floor_asymptotic
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound fractionalFloorTerm fractionalFloorMain
      secondaryCapacityRemainderScale := by
  have hscale : secondaryCapacityRemainderScale =
      fractionalMobiusRemainderScale := by
    funext N
    rfl
  rw [hscale]
  exact fractionalFloorTerm_asymptotic hSaffariVaughan

theorem continuous_secondary_coefficient
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound continuousCapacity continuousCapacityMain
    secondaryCapacityRemainderScale :=
  continuous_secondary_coefficient_of_fractional_and_tail
    secondaryCapacityRemainderScale secondaryCapacityRemainderScale_nonneg
    (fractional_floor_asymptotic hSaffariVaughan) reduced_euler_tail_estimate

/-- Main term of the manuscript's literal square-box GCD/LCM sum. -/
noncomputable def gcdLcmSquareMain (N : ℕ) : ℝ :=
  3 * (N : ℝ) - 3 * (Real.pi ^ 2)⁻¹ * Real.log N ^ 2

/-- Main term of the manuscript's literal one-sided GCD/LCM sum. -/
noncomputable def gcdLcmTriangularMain (N : ℕ) : ℝ :=
  2 * (N : ℝ) - (3 / 2 : ℝ) * (Real.pi ^ 2)⁻¹ * Real.log N ^ 2

theorem secondary_term_for_gcd_lcm_square
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound gcdLcmSquareSum gcdLcmSquareMain
      (fun N => 3 * secondaryCapacityRemainderScale N) := by
  have h := continuous_secondary_coefficient hSaffariVaughan
  rcases h with ⟨C, hC, N₀, hbound⟩
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN
  rw [gcdLcmSquareSum_eq_three_continuousCapacity]
  unfold gcdLcmSquareMain
  rw [show
      3 * continuousCapacity N -
          (3 * (N : ℝ) - 3 * (Real.pi ^ 2)⁻¹ * Real.log N ^ 2) =
        3 * (continuousCapacity N -
          ((N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    3 * |continuousCapacity N -
        ((N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)| ≤
      3 * (C * secondaryCapacityRemainderScale N) := by
        gcongr
        exact hbound N hN
    _ = C * (3 * secondaryCapacityRemainderScale N) := by ring

theorem secondary_term_for_gcd_lcm_triangular
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound gcdLcmTriangularSum gcdLcmTriangularMain
      (fun N => (3 / 2 : ℝ) * secondaryCapacityRemainderScale N) := by
  rcases continuous_secondary_coefficient hSaffariVaughan with
    ⟨C, hC, N₀, hbound⟩
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN
  rw [gcdLcmTriangularSum_eq_capacity]
  unfold gcdLcmTriangularMain
  rw [show
      ((N : ℝ) + 3 * continuousCapacity N) / 2 -
          (2 * (N : ℝ) - (3 / 2 : ℝ) * (Real.pi ^ 2)⁻¹ * Real.log N ^ 2) =
        (3 / 2 : ℝ) *
          (continuousCapacity N -
            ((N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)) by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  calc
    (3 / 2 : ℝ) *
        |continuousCapacity N -
          ((N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)| ≤
      (3 / 2 : ℝ) * (C * secondaryCapacityRemainderScale N) := by
        gcongr
        exact hbound N hN
    _ = C * ((3 / 2 : ℝ) * secondaryCapacityRemainderScale N) := by ring

theorem secondary_term_for_gcd_lcm_sum
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound gcdLcmSquareSum gcdLcmSquareMain
        (fun N => 3 * secondaryCapacityRemainderScale N) ∧
      EventualErrorBound gcdLcmTriangularSum gcdLcmTriangularMain
        (fun N => (3 / 2 : ℝ) * secondaryCapacityRemainderScale N) :=
  ⟨secondary_term_for_gcd_lcm_square hSaffariVaughan,
    secondary_term_for_gcd_lcm_triangular hSaffariVaughan⟩

end NField.Alignment.SecondaryCapacityAnalyticInputs
