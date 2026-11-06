/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaBilinearReduction

/-! # The literal inverse-product phase on ordered prime pairs -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaProductPhase
open scoped BigOperators
open KaratsubaBilinearReduction KaratsubaWeightedMoment

/-- Coprimality identifies the inverse of a natural product without a field assumption. -/
theorem inverse_nat_mul {m p q : ℕ} (hp : p.Coprime m) (hq : q.Coprime m) :
    ((p*q : ℕ) : ZMod m)⁻¹ = (p : ZMod m)⁻¹ * (q : ZMod m)⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  rw [Nat.cast_mul]
  calc
    (p : ZMod m) * q * ((p : ZMod m)⁻¹ * (q : ZMod m)⁻¹) =
        ((p : ZMod m) * (p : ZMod m)⁻¹) * ((q : ZMod m) * (q : ZMod m)⁻¹) := by ring
    _ = 1 := by rw [ZMod.coe_mul_inv_eq_one p hp, ZMod.coe_mul_inv_eq_one q hq, one_mul]

/-- The bilinear sum is over ordered pairs, retaining every representation of a product. -/
theorem bilinear_eq_ordered_inverse_sum {P Q : Finset ℕ} {m : ℕ} [NeZero m]
    (hP : ∀ p ∈ P, p.Coprime m) (hQ : ∀ q ∈ Q, q.Coprime m) (a b : ZMod m) :
    bilinearPrimeSum P Q a b =
      ∑ p : {p // p ∈ P}, ∑ q : {q // q ∈ Q},
        ZMod.stdAddChar (a * ((p.val*q.val : ℕ) : ZMod m)⁻¹ +
          b * ((p.val*q.val : ℕ) : ZMod m)) := by
  unfold bilinearPrimeSum primeRow mixedPrimeSum
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [inverse_nat_mul (hP _ p.property) (hQ _ q.property), Nat.cast_mul]
  congr 1
  ring

/-- Ordered prime pairs with separated factors have no product multiplicity. -/
theorem ordered_product_injective {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, q < p) :
    Function.Injective (fun u : {p // p ∈ P} × {q // q ∈ Q} => u.1.val * u.2.val) := by
  intro u v he
  change u.1.val * u.2.val = v.1.val * v.2.val at he
  have hp := hP _ u.1.property
  have hdiv : u.1.val ∣ v.1.val * v.2.val := by
    rw [← he]
    exact dvd_mul_right _ _
  have heq : u.1.val = v.1.val := by
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact ((hP _ v.1.property).dvd_iff_eq hp.ne_one).mp h |>.symm
    · have hh := ((hQ _ v.2.property).dvd_iff_eq hp.ne_one).mp h
      have hs := hsep _ u.1.property _ v.2.property
      omega
  have hq : u.2.val = v.2.val := by
    rw [← heq] at he
    exact Nat.eq_of_mul_eq_mul_left hp.pos he
  exact Prod.ext (Subtype.ext heq) (Subtype.ext hq)

end NField.Alignment.KaratsubaProductPhase
