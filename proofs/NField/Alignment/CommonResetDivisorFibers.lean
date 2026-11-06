/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDeterminants
import NField.Alignment.CommonResetGeometricMass

/-! # Counting the actual modulus fibers by a nonzero determinant -/

noncomputable section

namespace NField.Alignment.CommonResetDivisorFibers

open scoped BigOperators
open CommonResetDeterminants CommonResetGeometricMass

def divisorMaximum (p : ℕ) : ℕ :=
  (Finset.Icc 1 (2*p^3)).sup (fun n => n.divisors.card)

theorem divisor_card_le_maximum {p n : ℕ} (hn : 0 < n) (hnp : n ≤ 2*p^3) :
    n.divisors.card ≤ divisorMaximum p := by
  unfold divisorMaximum
  exact Finset.le_sup (f := fun n : ℕ => n.divisors.card) (Finset.mem_Icc.mpr ⟨hn, hnp⟩)

def centeredReciprocal (z : ℤ) : ℝ := if z = 0 then 0 else 1/|(z : ℝ)|

theorem centeredReciprocal_nonneg (z : ℤ) : 0 ≤ centeredReciprocal z := by
  unfold centeredReciprocal
  split_ifs <;> positivity

theorem centeredReciprocal_sum (R : ℕ) :
    (∑ z ∈ Finset.Icc (-(R : ℤ)) R, centeredReciprocal z) = 2*(harmonic R : ℝ) := by
  rw [sum_symmetric_Icc R _ (by simp [centeredReciprocal])
    (fun z => by simp [centeredReciprocal, abs_neg])]
  congr 1
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℤ) ≠ 0 := by
    have hpos := (Finset.mem_Icc.mp hn).1
    omega
  simp only [centeredReciprocal, if_neg hn0, Int.cast_natCast,
    abs_of_nonneg (show (0 : ℝ) ≤ n by positivity), one_div]

theorem weighted_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (address : α → β) (weight : β → ℝ)
    (hmap : ∀ a ∈ S, address a ∈ T) (B : ℕ)
    (hcard : ∀ b ∈ T, (S.filter (fun a => address a = b)).card ≤ B)
    (hweight : ∀ b ∈ T, 0 ≤ weight b) :
    (∑ a ∈ S, weight (address a)) ≤ (B : ℝ)*∑ b ∈ T, weight b := by
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun a => weight (address a)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have he : (∑ a ∈ S.filter (fun a => address a = b), weight (address a)) =
      ((S.filter (fun a => address a = b)).card : ℝ)*weight b := by
    simp only [Finset.sum_congr rfl (fun a ha => congrArg weight (Finset.mem_filter.mp ha).2),
      Finset.sum_const, nsmul_eq_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard b hb)) (hweight b hb)

/-- Title: `The full centered-residue sum counts each possible modulus by its divisor`. -/
theorem carrier_fiber_bound {p b u : ℕ} (hp : 2 ≤ p) (hb : 0 < b) (hbp : b < p)
    (hup : u < p) (S : Finset ℕ)
    (hS : ∀ t ∈ S, 0 < t ∧ t < p ∧ u.Coprime t) :
    (∑ t ∈ S, centeredReciprocal (centeredCarrier p b u t)) ≤
      2*(divisorMaximum p : ℝ)*(harmonic p : ℝ) := by
  classical
  have hmap : ∀ t ∈ S, centeredCarrier p b u t ∈ Finset.Icc (-(p : ℤ)) p := by
    intro t ht
    have htdata := hS t ht
    have hz := centeredCarrier_bound (p := p) (b := b) (u := u) htdata.1
    have htp : (t : ℤ) < p := by exact_mod_cast htdata.2.1
    rw [Finset.mem_Icc]
    have habs := abs_le.mp (show |centeredCarrier p b u t| ≤ (p : ℤ) by
      linarith [abs_nonneg (centeredCarrier p b u t)])
    exact habs
  have hcard (z : ℤ) (_hz : z ∈ Finset.Icc (-(p : ℤ)) p) :
      (S.filter (fun t => centeredCarrier p b u t = z)).card ≤ divisorMaximum p := by
    by_cases he : (S.filter (fun t => centeredCarrier p b u t = z)).Nonempty
    · obtain ⟨t, ht⟩ := he
      have htf := Finset.mem_filter.mp ht
      have htdata := hS t htf.1
      have hr := carrier_determinant_range hp htdata.1 htdata.2.1 hb hbp hup
      rw [htf.2] at hr
      have hc := carrier_moduli_count z (S.filter (fun t => centeredCarrier p b u t = z)) hr.1
        (fun m hm => by
          have hmdata := Finset.mem_filter.mp hm
          have hmd := hS m hmdata.1
          have hd := centeredCarrier_congruence (p := p) (b := b) hmd.1 hmd.2.2
          rwa [hmdata.2] at hd)
      apply hc.trans
      apply divisor_card_le_maximum
      · omega
      · have hh : (p : ℤ)^2*(b : ℤ)-(u : ℤ)*z ≤ (2*p^3 : ℕ) := by
          push_cast
          exact hr.2.le
        omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp
  have hbound := weighted_fiber_bound S (Finset.Icc (-(p : ℤ)) p)
    (fun t => centeredCarrier p b u t) centeredReciprocal hmap (divisorMaximum p)
    hcard (fun z _ => centeredReciprocal_nonneg z)
  rw [centeredReciprocal_sum] at hbound
  nlinarith

end NField.Alignment.CommonResetDivisorFibers
