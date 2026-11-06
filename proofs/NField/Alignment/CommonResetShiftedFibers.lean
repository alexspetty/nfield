/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetShiftedDeterminants
import NField.Alignment.CommonResetDivisorFibers

/-! # Counting all three endpoint determinant fibers -/

noncomputable section

namespace NField.Alignment.CommonResetShiftedFibers

open scoped BigOperators
open CommonResetDivisorFibers CommonResetShiftedDeterminants

theorem positive_divisor_count (D : ℤ) (hD : 0 < D) (S : Finset ℕ)
    (hS : ∀ t ∈ S, (t : ℤ) ∣ D) : S.card ≤ D.toNat.divisors.card := by
  apply Finset.card_le_card
  intro t ht
  apply Nat.mem_divisors.mpr
  constructor
  · have hd := hS t ht
    rw [← Int.toNat_of_nonneg hD.le] at hd
    exact_mod_cast hd
  · omega

/-- Title: `Each shifted endpoint residue has at most the actual divisor maximum of moduli`. -/
theorem shifted_fiber_bound {p v u : ℕ} (hp : 2 ≤ p) (hv : 0 < v)
    (hvp : 2*v < p) (hup : 2*u < p) (η : ℤ) (hη : |η| ≤ 1)
    (S : Finset ℕ) (hS : ∀ t ∈ S, 0 < t ∧ t < p ∧ u.Coprime t) :
    (∑ t ∈ S, centeredReciprocal (centeredEndpointPhase p v u t η)) ≤
      2*(divisorMaximum p : ℝ)*(harmonic p : ℝ) := by
  classical
  have hmap : ∀ t ∈ S, centeredEndpointPhase p v u t η ∈ Finset.Icc (-(p : ℤ)) p := by
    intro t ht
    have htd := hS t ht
    have hz := centeredEndpointPhase_bound (p := p) (v := v) (u := u) htd.1 η
    have htp : (t : ℤ) < p := by exact_mod_cast htd.2.1
    rw [Finset.mem_Icc]
    exact abs_le.mp (hz.trans htp.le)
  have hcard (z : ℤ) (_hz : z ∈ Finset.Icc (-(p : ℤ)) p) :
      (S.filter (fun t => centeredEndpointPhase p v u t η = z)).card ≤ divisorMaximum p := by
    by_cases he : (S.filter (fun t => centeredEndpointPhase p v u t η = z)).Nonempty
    · obtain ⟨t, ht⟩ := he
      have htf := Finset.mem_filter.mp ht
      have htd := hS t htf.1
      have hr := shifted_determinant_range hp htd.1 htd.2.1 hv hvp hup η hη
      rw [htf.2] at hr
      have hc := positive_divisor_count (shiftedDeterminant p v u η z) hr.1
        (S.filter (fun t => centeredEndpointPhase p v u t η = z)) (fun m hm => by
          have hmf := Finset.mem_filter.mp hm
          have hmd := hS m hmf.1
          have hd := shifted_determinant_congruence (p := p) (v := v) hmd.1 hmd.2.2 η
          rw [hmf.2] at hd
          exact dvd_trans (dvd_mul_left (m : ℤ) 2) hd)
      apply hc.trans
      apply divisor_card_le_maximum
      · omega
      · have hh : shiftedDeterminant p v u η z ≤ (2*p^3 : ℕ) := by
          push_cast
          exact hr.2.le
        omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp
  have hbound := weighted_fiber_bound S (Finset.Icc (-(p : ℤ)) p)
    (fun t => centeredEndpointPhase p v u t η) centeredReciprocal hmap (divisorMaximum p)
    hcard (fun z _ => centeredReciprocal_nonneg z)
  rw [centeredReciprocal_sum] at hbound
  nlinarith

end NField.Alignment.CommonResetShiftedFibers
