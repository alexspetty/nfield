/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetEndpoint

/-! # Exact half-range frequency pairing -/

noncomputable section

namespace NField.Alignment.CommonResetHalfFrequencies

open scoped BigOperators
open CommonResetFourier CommonResetKernel CommonResetEndpoint

theorem involution_sum_pair {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ α) (he : ∀ a, e (e a) = a) (rank : α → ℕ)
    (hrank : Function.Injective rank) (f : α → ℝ)
    (hf : ∀ a, f (e a) = f a) (hfix : ∀ a, e a = a → f a = 0) :
    (∑ a, f a) = 2*∑ a ∈ Finset.univ.filter (fun a => rank a < rank (e a)), f a := by
  let g := fun a => if rank a < rank (e a) then f a else 0
  have hpoint (a : α) : f a = g a+g (e a) := by
    dsimp only [g]
    rw [he, hf]
    rcases lt_trichotomy (rank a) (rank (e a)) with h|h|h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · have hea : e a = a := hrank h.symm
      rw [if_neg (by omega), if_neg (by omega), hfix a hea]
      norm_num
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have hs := Equiv.sum_comp e g
  calc
    (∑ a, f a) = ∑ a, (g a+g (e a)) := Finset.sum_congr rfl (fun a _ => hpoint a)
    _ = 2*∑ a, g a := by rw [Finset.sum_add_distrib, hs]; ring
    _ = _ := by simp only [g, Finset.sum_ite, Finset.sum_const_zero, add_zero]

theorem residue_lower_half {t : ℕ} [NeZero t] (a : ZMod t) :
    a.val < (-a).val ↔ 0 < a.val ∧ 2*a.val < t := by
  by_cases ha : a = 0
  · subst a
    simp
  · letI : NeZero a := ⟨ha⟩
    rw [ZMod.val_neg_of_ne_zero]
    have hpos : 0 < a.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero a).not.mpr ha)
    have hlt := a.val_lt
    omega

def lowerResidues (t : ℕ) [NeZero t] : Finset (ZMod t) :=
  Finset.univ.filter (fun a => 0 < a.val ∧ 2*a.val < t)

def lowerUnits (t : ℕ) [NeZero t] : Finset (ZMod t)ˣ :=
  Finset.univ.filter (fun u => 0 < u.val.val ∧ 2*u.val.val < t)

theorem residue_sum_pair {t : ℕ} [NeZero t] (f : ZMod t → ℝ)
    (hf : ∀ a, f (-a) = f a) (hfix : ∀ a, -a = a → f a = 0) :
    (∑ a, f a) = 2*∑ a ∈ lowerResidues t, f a := by
  simpa only [Equiv.neg_apply, residue_lower_half, lowerResidues] using
    involution_sum_pair (Equiv.neg (ZMod t)) (fun a => neg_neg a)
      ZMod.val (ZMod.val_injective t) f hf hfix

theorem unit_sum_pair {t : ℕ} [NeZero t] (f : (ZMod t)ˣ → ℝ)
    (hf : ∀ a, f (-a) = f a) (hfix : ∀ a, -a = a → f a = 0) :
    (∑ a, f a) = 2*∑ a ∈ lowerUnits t, f a := by
  have hrank : Function.Injective (fun u : (ZMod t)ˣ => u.val.val) :=
    (ZMod.val_injective t).comp Units.val_injective
  simpa only [Equiv.neg_apply, Units.val_neg, residue_lower_half, lowerUnits] using
    involution_sum_pair (Equiv.neg (ZMod t)ˣ) (fun a => neg_neg a)
      (fun u => u.val.val) hrank f hf hfix

theorem cotangent_fixed_zero {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    (a : ZMod t) (ha : -a = a) : cotangentResidue a = 0 := by
  have h := cotangentResidue_odd ht a
  rw [ha] at h
  linarith

def endpointFrequency {t : ℕ} [NeZero t] (q r : ℕ) (u : (ZMod t)ˣ) (v : ZMod t) : ℝ :=
  cotangentResidue u.val*cotangentResidue v*
    endpointDifference r ((q : ZMod t)*v*(↑(u⁻¹) : ZMod t))

theorem endpointFrequency_even_right {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    (q r : ℕ) (u : (ZMod t)ˣ) (v : ZMod t) :
    endpointFrequency q r u (-v) = endpointFrequency q r u v := by
  simp only [endpointFrequency, cotangentResidue_odd ht, mul_neg, neg_mul,
    endpointDifference_odd, neg_neg]

theorem endpointFrequency_even_left {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    (q r : ℕ) (u : (ZMod t)ˣ) (v : ZMod t) :
    endpointFrequency q r (-u) v = endpointFrequency q r u v := by
  simp only [endpointFrequency, Units.val_neg, cotangentResidue_odd ht, inv_neg,
    mul_neg, neg_mul, endpointDifference_odd, neg_neg]

/-- Title: `Zero and half-period terms vanish in the four sign pairing`. -/
theorem endpoint_frequency_half_pair {t : ℕ} [NeZero t] (ht : 2 ≤ t) (q r : ℕ) :
    (∑ u : (ZMod t)ˣ, ∑ v : ZMod t, endpointFrequency q r u v) =
      4*∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t, endpointFrequency q r u v := by
  have hv (u : (ZMod t)ˣ) : (∑ v, endpointFrequency q r u v) =
      2*∑ v ∈ lowerResidues t, endpointFrequency q r u v := by
    apply residue_sum_pair
    · exact endpointFrequency_even_right ht q r u
    · intro v hv
      simp only [endpointFrequency, cotangent_fixed_zero ht v hv, mul_zero, zero_mul]
  simp only [hv, ← Finset.mul_sum]
  have hu : (∑ u : (ZMod t)ˣ, ∑ v ∈ lowerResidues t, endpointFrequency q r u v) =
      2*∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t, endpointFrequency q r u v := by
    apply unit_sum_pair
    · intro u
      exact Finset.sum_congr rfl (fun v _ => endpointFrequency_even_left ht q r u v)
    · intro u hu
      have hval : -u.val = u.val := by simpa only [Units.val_neg] using congrArg Units.val hu
      simp only [endpointFrequency, cotangent_fixed_zero ht u.val hval, zero_mul,
        Finset.sum_const_zero]
  rw [hu]
  ring

/-- Title: `The terminal kernel prefix is the complete half-range endpoint expression`. -/
theorem completed_half_kernel {t q : ℕ} [NeZero t] (ht : 2 ≤ t)
    (hq : q.Coprime t) (r : ℕ) (hr : r < t) :
    2*(∑ a ∈ Finset.Icc 1 r, CommonResetConductor.conductorKernel t
      (DedekindInverseResidueTransform.inverseResidue q t*a)) =
      ∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t, endpointFrequency q r u v := by
  rw [completed_kernel_sum ht hq r hr]
  change (1/4 : ℝ)*(∑ u : (ZMod t)ˣ, ∑ v : ZMod t, endpointFrequency q r u v) = _
  rw [endpoint_frequency_half_pair ht]
  ring

def completedConductor (N q t : ℕ) : ℝ :=
  if ht : 2 ≤ t then
    letI : NeZero t := ⟨by omega⟩
    (harmonic (N/t) : ℝ)/(t : ℝ)*
      ∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t, endpointFrequency q (N%t) u v
  else 0

/-- Title: `The entire interior source has the printed completed endpoint formula`. -/
theorem completed_source (N q : ℕ) (hq : ∀ k ∈ Finset.Icc 1 N, q.Coprime k) :
    CommonResetSampling.interiorSource N q = ∑ t ∈ Finset.Icc 2 N, completedConductor N q t := by
  rw [CommonResetLift.full_lift_weight N q hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htr := Finset.mem_Icc.mp ht
  letI : NeZero t := ⟨by omega⟩
  rw [completedConductor, dif_pos htr.1]
  have he := completed_half_kernel htr.1 (hq t (Finset.mem_Icc.mpr ⟨by omega, htr.2⟩))
    (N%t) (Nat.mod_lt N (by omega))
  rw [← he]
  ring

end NField.Alignment.CommonResetHalfFrequencies
