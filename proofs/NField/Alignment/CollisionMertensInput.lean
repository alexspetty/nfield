/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.External.ConservationPNT.IEANTN.Mertens

/-!
# Literal Mertens inputs for collision alignment

The proved upstream Mertens theorem is specialized to the exact inverse
prime product and logarithm-weighted prime sum in the manuscript.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMertensInput

open scoped BigOperators
open Filter Asymptotics

def primesUpTo (x : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
def inversePrimeProduct (x : ℝ) : ℝ := ∏ p ∈ primesUpTo x, (1-(p : ℝ)⁻¹)⁻¹
def logPrimeSum (x : ℝ) : ℝ := ∑ p ∈ primesUpTo x, Real.log p/(p : ℝ)

theorem primesUpTo_mem {x : ℝ} {p : ℕ} :
    p ∈ primesUpTo x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp0,hpx⟩,hp⟩
    exact ⟨hp,(Nat.le_floor_iff' hp0.ne').mp hpx⟩
  · rintro ⟨hp,hpx⟩
    have hx : 0 ≤ x := (Nat.cast_nonneg p).trans hpx
    exact ⟨⟨hp.pos,(Nat.le_floor_iff hx).mpr hpx⟩,hp⟩

theorem inversePrimeProduct_eq (x : ℝ) :
    inversePrimeProduct x=(∏ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
      (1-(1 : ℝ)/p))⁻¹ := by
  simp only [inversePrimeProduct,primesUpTo,one_div,Finset.prod_inv_distrib]

theorem inversePrimeProduct_pos (x : ℝ) : 0 < inversePrimeProduct x := by
  apply Finset.prod_pos
  intro p hp
  have hpp := (primesUpTo_mem.mp hp).1
  apply inv_pos.mpr
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

theorem mertens_inverse_product :
    inversePrimeProduct ~[atTop] (fun x : ℝ => Real.exp Real.eulerMascheroniConstant*Real.log x) := by
  have h := Mertens.E₃.bound''.inv
  convert! h using 1
  · ext x
    exact inversePrimeProduct_eq x
  · ext x
    simp [Real.exp_neg,div_eq_mul_inv,mul_comm]

theorem logPrimeSum_error_bound {x : ℝ} (hx : 1 ≤ x) :
    |logPrimeSum x-Real.log x| ≤ Real.log 4+4 :=
  Mertens.sum_log_prime_div_eq_log hx

theorem logPrimeSum_error_isBigO :
    (fun x : ℝ => logPrimeSum x-Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  Mertens.sum_log_prime_div_eq_log'

theorem literal_mertens_inputs :
    inversePrimeProduct ~[atTop] (fun x : ℝ => Real.exp Real.eulerMascheroniConstant*Real.log x) ∧
    (fun x : ℝ => logPrimeSum x-Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  ⟨mertens_inverse_product,logPrimeSum_error_isBigO⟩

end NField.Alignment.CollisionMertensInput
