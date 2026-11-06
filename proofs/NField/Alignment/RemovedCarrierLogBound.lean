/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SquareLockCutoffLimits
import NField.Alignment.CarrierTriangularIdentity

/-! # The literal full-minus-live ledger and its logarithmic removed mass -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RemovedCarrierLogBound
open PrimeSquareCubicEnergy
open scoped BigOperators Topology Classical
open Filter Asymptotics LiveCarrierDamping CarrierStateSwitching
  SquareLockAsymptoticScales SquareLockCutoffLimits SquareLockCarrierMass
  CarrierTriangularIdentity ComplementaryPartition DedekindAbelRemainder

theorem selected_full_fresh {p X : ℕ} [NeZero X] (hX : 3 ≤ X) (hXp : X<p) :
    selectedCarrierFresh p (fullCarrierSet p) X=freshCarrierSum (p^2) X := by
  unfold selectedCarrierFresh
  rw [Finset.sum_filter]
  exact full_fresh_sum_natural hX hXp

/-- Title: `The full and live fresh sums differ by the removed carrier sum`. -/
theorem full_live_difference (p : ℕ) :
    (∑ X ∈ Finset.Icc 3 (p-1), carrierDwell (p-1) X*
      ((selectedCarrierFresh p (fullCarrierSet p) X : ℝ)-
        (selectedCarrierFresh p (liveCarrierSet p) X : ℝ)))=
      carrierFamilyFreshMass p (removedCarrierSet p) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  change carrierFamilyFreshMass p (fullCarrierSet p)-
      carrierFamilyFreshMass p (liveCarrierSet p)=_
  rw [full_live_removed_split]
  ring

theorem full_live_difference_slices {p : ℕ} (hp : p.Prime) :
    (∑ X ∈ Finset.Icc 3 (p-1), carrierDwell (p-1) X*
      ((selectedCarrierFresh p (fullCarrierSet p) X : ℝ)-
        (selectedCarrierFresh p (liveCarrierSet p) X : ℝ)))=
      (∑ k ∈ removedCarrierSet p,modulusKSlice p k).re := by
  rw [full_live_difference]
  exact carrierFamilyFreshMass_eq_modulusKSlices hp _ (Finset.filter_subset _ _)

/-- Title: `The removed carrier mass is bounded by p squared times log p`. -/
theorem removed_carrier_log_bound :
    (fun p => carrierFamilyFreshMass p (removedCarrierSet p)) =O[primeAtTop]
      (fun p => (p : ℝ)^2*Real.log (p : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_collar_isBigO_log.exists_nonneg
  apply IsBigO.of_bound (C/8)
  have hp : ∀ᶠ p in primeAtTop,p.Prime :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hp => hp)
  filter_upwards [hp,hbound.bound] with p hp hb
  have hl : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  rw [Real.norm_of_nonneg (collarMass_nonneg _ _),Real.norm_of_nonneg hl] at hb
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hl)]
  calc
    _ ≤ (p : ℝ)^2/8*squareLockCollarMass p (coefficientSquareLockCutoff p) :=
      abs_removedCarrierFreshMass_le_squareLockMass hp
    _ ≤ (p : ℝ)^2/8*(C*Real.log (p : ℝ)) := by gcongr
    _ = _ := by ring

theorem full_live_difference_log_bound :
    (fun p => ∑ X ∈ Finset.Icc 3 (p-1),carrierDwell (p-1) X*
      ((selectedCarrierFresh p (fullCarrierSet p) X : ℝ)-
        (selectedCarrierFresh p (liveCarrierSet p) X : ℝ))) =O[primeAtTop]
      (fun p => (p : ℝ)^2*Real.log (p : ℝ)) := by
  simp_rw [full_live_difference]
  exact removed_carrier_log_bound

end NField.Alignment.RemovedCarrierLogBound
