/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreResetReading
/-! # The printed initial basis trace, including its reset coordinate -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators
open NField.Alignment CommonResetGram CollisionRampEnergy CommonResetSampling
open CommonResetGrid DedekindReciprocity FibreReconstruction

def basisSource (j : ℕ) (n : ℕ) : ℝ := if n=j then 1 else 0

theorem coherent_fibre_assigned_origin_zero {p : ℕ} (hp : p.Prime) (v : Fin p) :
    fibrePath p (fun _ => 1) 0 v=0 := by
  unfold fibrePath
  simp only [add_zero, coherent_prime_grid_zero hp]
  simp [weightedProfile, midpointRow]

theorem basis_profile {N j : ℕ} (hj : j ∈ Finset.Icc 1 N) (x : ℝ) :
    weightedProfile N (basisSource j) x=2*midpointRow j x := by
  simp [weightedProfile, basisSource, ite_mul, hj]

theorem basis_contact_mass {N j : ℕ} (hj : j ∈ Finset.Icc 1 N) (x : ℝ) :
    contactMass N (basisSource j) x=if Int.fract ((j : ℝ)*x)=0 then 1 else 0 := by
  unfold contactMass
  rw [Finset.sum_eq_single j]
  · simp [basisSource]
  · intro b hb hbj
    simp [basisSource, hbj]
  · intro h
    exact (h hj).elim

theorem basis_profile_right {N j : ℕ} (hj : j ∈ Finset.Icc 1 N) (x : ℝ) :
    profileRight N (basisSource j) x=
      2*midpointRow j x-(if Int.fract ((j : ℝ)*x)=0 then 1 else 0) := by
  rw [profileRight, basis_profile hj, basis_contact_mass hj]

theorem basis_initial_fibre_trace {p j : ℕ} (hp : p.Prime)
    (hj : j ∈ Finset.Icc 1 (p-1)) (v : Fin p) :
    (p : ℝ)*fibreRight p (basisSource j) 0 v=
      2*((j*v.val%p : ℕ) : ℝ)-((p-1 : ℕ) : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  unfold fibreRight
  rw [basis_profile_right hj, basis_profile_right hj]
  have hzero : midpointRow j 0=0 := by simp [midpointRow]
  simp only [add_zero, mul_zero, Int.fract_zero, if_true, hzero, zero_sub]
  rw [midpointRow_rational hp.pos]
  have hfrac : Int.fract ((j : ℝ)*((v.val : ℝ)/(p : ℝ)))=0 ↔ j*v.val%p=0 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod,
      div_eq_zero_iff]
    simp only [Nat.cast_eq_zero, hp.ne_zero, or_false]
  unfold rationalSawtooth
  rw [hN]
  simp only [hfrac]
  by_cases hrem : j*v.val%p=0 <;> simp [hrem] <;> field_simp <;> ring

end NField.ResetForests.FibreTraces
