/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.GramSectors
import NField.Alignment.CollisionJordanVariance
/-! # Literal primitive fields and their Jordan masses -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators
open NField.Alignment CollisionRampEnergy CommonResetGram CollisionJordanVariance

def jordanMass (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ)*(d : ℝ)^2

theorem jordan_mass_eq (n : ℕ) : jordanMass n=jordanTwo n := by
  by_cases hn : n=0
  · subst n
    simp [jordanMass]
  · have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := jordanTwo) (g := fun n : ℕ => (n : ℝ)^2)).mp
        (fun m hm => sum_jordanTwo_divisors m) n (Nat.pos_of_ne_zero hn)
    rw [Nat.sum_divisorsAntidiagonal'
      (fun a b : ℕ => (ArithmeticFunction.moebius a : ℝ)*(b : ℝ)^2)] at h
    exact h

theorem jordan_mass_pos {n : ℕ} (hn : 0 < n) : 0 < jordanMass n := by
  rw [jordan_mass_eq, jordanTwo_euler_product hn.ne']
  apply mul_pos (sq_pos_of_pos (by exact_mod_cast hn))
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hsq : (1 : ℝ) < (p : ℝ)^2 := by nlinarith
  have hi := inv_lt_one_of_one_lt₀ hsq
  linarith

theorem gcd_jordan_divisor_sum {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    (∑ d ∈ m.divisors, if d ∣ k then jordanMass d else 0)=(k.gcd m : ℝ)^2 := by
  have hset : m.divisors.filter (fun d => d ∣ k)=(k.gcd m).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg := (Nat.gcd_pos_of_pos_left m hk).ne'
    have hm0 := hm.ne'
    tauto
  rw [← Finset.sum_filter, hset]
  simp only [jordan_mass_eq]
  exact sum_jordanTwo_divisors _

def scaledSaw (n : ℕ) (x : ℝ) : ℝ := 2*(n : ℝ)*midpointRow n x

def primitiveField (n : ℕ) : ℝ → ℝ :=
  ∑ d ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius d.1 • scaledSaw d.2

theorem primitive_field_formula (n : ℕ) (x : ℝ) :
    primitiveField n x=2*∑ d ∈ n.divisors,
      (d : ℝ)*(ArithmeticFunction.moebius (n/d) : ℝ)*midpointRow d x := by
  rw [primitiveField, Nat.sum_divisorsAntidiagonal'
    (fun a b : ℕ => ArithmeticFunction.moebius a • scaledSaw b)]
  simp only [← Int.cast_smul_eq_zsmul ℝ, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, scaledSaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem scaled_saw_primitive_sum {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, primitiveField d)=scaledSaw n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := primitiveField) (g := scaledSaw)).mpr (fun _ _ => rfl) n hn

def primitiveSource (n j : ℕ) : ℝ :=
  if j ∣ n then (j : ℝ)*(ArithmeticFunction.moebius (n/j) : ℝ) else 0

theorem primitive_field_source {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) (x : ℝ) :
    weightedProfile N (primitiveSource n) x=primitiveField n x := by
  have hset : (Finset.Icc 1 N).filter (fun d => d ∣ n)=n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hn.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnN⟩,hd⟩
  rw [weightedProfile, primitive_field_formula]
  simp only [primitiveSource, ite_mul, zero_mul]
  rw [← Finset.sum_filter, hset]

end NField.ResetForests.PrimitiveCoordinates
