/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.LiveCarrierDamping

/-! # Every selected carrier ledger, including the small cutoff endpoints -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondarySwitchingLedger
open scoped BigOperators Classical
open CarrierStateSwitching FloorStateSwitchingLedger LiveCarrierDamping PrimeSquareCubicEnergy DedekindAbelRemainder

/-- Title: `The exact switching ledger includes every cutoff endpoint`. -/
theorem exact_selected_ledger
    {p N : ℕ} (hp : p.Prime)
    (carriers : Finset ℕ)
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k ∧ k < p) :
    dwellBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          (selectedCarrierFresh p carriers X : ℝ) ∧
    quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          ((carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2 +
            2 * carrierStateBurdenReal p carriers (X - 1) *
              (carrierStateBurdenReal p carriers X -
                carrierStateBurdenReal p carriers (X - 1))) ∧
    (let J := fun X =>
        carrierStateBurdenReal p carriers (X - 1) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) +
          (1 / 2 : ℝ) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2;
      (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * positivePart (J X)) =
        (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * negativePart (J X)) +
        quadraticBurden N (carrierDwell N)
          (carrierStateBurdenReal p carriers) / 2) := by
  by_cases hN : 3 ≤ N
  · exact exact_carrier_switching_ledger hp hN carriers hcarriers
  · have hI : Finset.Icc 3 N=∅ := Finset.Icc_eq_empty (by omega)
    simp [dwellBurden,quadraticBurden,hI]

/-- Title: `The fresh collision formula includes the first floor states`. -/
theorem fresh_collision_all_states {p : ℕ} (hp : p.Prime)
    (carriers : Finset ℕ) (hcarriers : ∀ k ∈ carriers,2 ≤ k ∧ k<p) (X : ℕ) :
    freshCarrierIncrement p carriers X=selectedCarrierFresh p carriers X := by
  by_cases hX : 3 ≤ X
  · exact freshCarrierIncrement_eq hp hX carriers hcarriers
  · have hnew : carrierStateBurden p carriers X=0 := by
      unfold carrierStateBurden
      apply Finset.sum_eq_zero
      intro k hk
      have hk2 := (hcarriers k hk).1
      simp [show ¬k<X by omega]
    have hold : carrierStateBurden p carriers (X-1)=0 := by
      unfold carrierStateBurden
      apply Finset.sum_eq_zero
      intro k hk
      have hk2 := (hcarriers k hk).1
      simp [show ¬k<X-1 by omega]
    have hf : selectedCarrierFresh p carriers X=0 := by
      unfold selectedCarrierFresh
      apply Finset.sum_eq_zero
      intro k hk
      have hh := (Finset.mem_filter.mp hk).2
      omega
    rw [freshCarrierIncrement,hnew,hold,hf,sub_self]

/-- Title: `The selected carrier sum equals both switching coordinates`. -/
theorem selected_linear_ledger {p : ℕ} (hp : p.Prime) (carriers : Finset ℕ)
    (hcarriers : carriers ⊆ fullCarrierSet p) :
    (∑ k ∈ carriers,modulusKSlice p k).re=
      dwellBurden (p-1) (carrierDwell (p-1)) (carrierStateBurdenReal p carriers) ∧
    dwellBurden (p-1) (carrierDwell (p-1)) (carrierStateBurdenReal p carriers)=
      carrierFamilyFreshMass p carriers := by
  have hk : ∀ k ∈ carriers,2 ≤ k ∧ k<p := by
    intro k hk
    have hh := Finset.mem_Icc.mp (hcarriers hk)
    exact ⟨hh.1,by omega⟩
  have hledger := (exact_selected_ledger (N:=p-1) hp carriers hk).1
  change dwellBurden (p-1) (carrierDwell (p-1)) (carrierStateBurdenReal p carriers)=
    carrierFamilyFreshMass p carriers at hledger
  exact ⟨(carrierFamilyFreshMass_eq_modulusKSlices hp carriers hcarriers).symm.trans hledger.symm,hledger⟩

end NField.Alignment.SecondarySwitchingLedger
