/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetLift

/-! # Literal endpoint indicators in the completed conductor sum -/

noncomputable section

namespace NField.Alignment.CommonResetEndpoint

open scoped BigOperators
open CommonResetFourier CommonResetConductor CommonResetKernel CommonResetLift
open CommonResetSampling DedekindInverseResidueTransform

def prefixIndicator {t : ℕ} [NeZero t] (r : ℕ) (a : ZMod t) : ℝ :=
  if a.val ∈ Finset.Icc 1 r then 1 else 0

def endpointDifference {t : ℕ} [NeZero t] (r : ℕ) (a : ZMod t) : ℝ :=
  prefixIndicator r a-prefixIndicator r (-a)

/-- Title: `The endpoint indicator retains both inclusive endpoints`. -/
theorem endpointDifference_formula {t : ℕ} [NeZero t] (r : ℕ) (a : ZMod t) :
    endpointDifference r a = if a = 0 then 0 else
      (if a.val ≤ r then 1 else 0)-(if t-a.val ≤ r then 1 else 0) := by
  by_cases ha : a = 0
  · subst a
    simp [endpointDifference, prefixIndicator]
  · have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha (ZMod.val_injective t
      (by simpa only [ZMod.val_zero] using h)))
    letI : NeZero a := ⟨ha⟩
    have hneg := ZMod.val_neg_of_ne_zero a
    have halt := a.val_lt
    simp only [endpointDifference, prefixIndicator, if_neg ha, hneg, Finset.mem_Icc]
    have hleft : 1 ≤ a.val := ha0
    have hright : 1 ≤ t-a.val := by omega
    simp only [hleft, hright, true_and]

theorem endpointDifference_odd {t : ℕ} [NeZero t] (r : ℕ) (a : ZMod t) :
    endpointDifference r (-a) = -endpointDifference r a := by
  simp only [endpointDifference, neg_neg]
  ring

theorem endpointDifference_zero {t : ℕ} [NeZero t] (r : ℕ) :
    endpointDifference r (0 : ZMod t) = 0 := by
  simp [endpointDifference]

theorem prefixIndicator_sum {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t)
    (f : ZMod t → ℝ) :
    (∑ a : ZMod t, prefixIndicator r a*f a) =
      ∑ a ∈ Finset.Icc 1 r, f (a : ZMod t) := by
  have hgrid := CommonResetGrid.sum_residue_values (m := t)
    (fun a => prefixIndicator r (a : ZMod t)*f (a : ZMod t))
  simp only [ZMod.natCast_zmod_val] at hgrid
  rw [hgrid]
  simp only [prefixIndicator, ite_mul, Finset.sum_ite, one_mul, zero_mul, Finset.sum_const_zero, add_zero]
  have hset : (Finset.range t).filter (fun a : ℕ => (a : ZMod t).val ∈ Finset.Icc 1 r) =
      Finset.Icc 1 r := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, ZMod.val_natCast, Finset.mem_Icc]
    constructor
    · intro h
      simpa only [Nat.mod_eq_of_lt h.1] using h.2
    · intro h
      have hat : a < t := lt_of_le_of_lt h.2 hr
      exact ⟨hat, by simpa only [Nat.mod_eq_of_lt hat] using h⟩
  rw [hset]

/-- Title: `Oddness converts twice the prefix into the signed endpoint response`. -/
theorem odd_prefix_completion {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t)
    (f : ZMod t → ℝ) (hf : ∀ a, f (-a) = -f a) :
    2*(∑ a ∈ Finset.Icc 1 r, f (a : ZMod t)) =
      ∑ a : ZMod t, endpointDifference r a*f a := by
  rw [← prefixIndicator_sum r hr f]
  simp only [endpointDifference, sub_mul, Finset.sum_sub_distrib]
  have he := Equiv.sum_comp (Equiv.neg (ZMod t))
    (fun a => prefixIndicator r (-a)*f a)
  simp only [Equiv.neg_apply, neg_neg, hf, mul_neg, Finset.sum_neg_distrib] at he
  rw [← he]
  ring

/-- Title: `The full-period endpoint response has the exact cotangent double sum`. -/
theorem completed_kernel_sum {t q : ℕ} [NeZero t] (ht : 2 ≤ t)
    (hq : q.Coprime t) (r : ℕ) (hr : r < t) :
    2*(∑ a ∈ Finset.Icc 1 r, conductorKernel t (inverseResidue q t*a)) =
      (1/4 : ℝ)*∑ u : (ZMod t)ˣ, ∑ v : ZMod t,
        cotangentResidue u.val*cotangentResidue v*
          endpointDifference r ((q : ZMod t)*v*(↑(u⁻¹) : ZMod t)) := by
  let Q : (ZMod t)ˣ := ZMod.unitOfCoprime q hq
  have hinv : (inverseResidue q t : ZMod t) = (↑(Q⁻¹) : ZMod t) := by
    unfold inverseResidue
    rw [dif_neg (by omega : t ≠ 0), dif_pos hq, ZMod.natCast_zmod_val]
  have hqval : Q.val = (q : ZMod t) := ZMod.coe_unitOfCoprime q hq
  have he (a : ℕ) : conductorKernel t (inverseResidue q t*a) =
      unitKernel ((↑(Q⁻¹) : ZMod t)*(a : ZMod t)) := by
    rw [conductorKernel_eq_units ht, Nat.cast_mul, hinv]
  simp only [he]
  rw [odd_prefix_completion r hr (fun a : ZMod t => unitKernel ((↑(Q⁻¹) : ZMod t)*a)) (fun a => by
    rw [mul_neg, unitKernel_odd ht])]
  unfold unitKernel
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  let w : (ZMod t)ˣ := Q⁻¹*u
  have hchange := Equiv.sum_comp w.mulLeft (fun v : ZMod t =>
    (1/4 : ℝ)*(cotangentResidue u.val*cotangentResidue v*
      endpointDifference r ((q : ZMod t)*v*(↑(u⁻¹) : ZMod t))))
  simp only [Units.mulLeft_apply] at hchange
  rw [← hchange]
  apply Finset.sum_congr rfl
  intro a _
  have hcancel : (q : ZMod t)*(w.val*a)*(↑(u⁻¹) : ZMod t) = a := by
    rw [← hqval]
    dsimp [w]
    calc
      Q.val*((↑(Q⁻¹) : ZMod t)*u.val*a)*(↑(u⁻¹) : ZMod t) =
          (Q.val*(↑(Q⁻¹) : ZMod t))*(u.val*(↑(u⁻¹) : ZMod t))*a := by ring
      _ = a := by simp
  rw [hcancel]
  dsimp [w]
  have harg : (↑(Q⁻¹) : ZMod t)*a*u.val = (↑(Q⁻¹) : ZMod t)*u.val*a := by ring
  rw [harg]
  ring

end NField.Alignment.CommonResetEndpoint
