/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.Alignment.CommonResetGrid
/-! # Recovering a reset from its two actual neighbouring grid readings

The sampler is finer than every product of source denominators. No
nonunit harmonic is deleted. The lower and upper integer quotients are
derived before they are inserted into the midpoint field.
-/

noncomputable section

namespace NField.ResetForests.SourceMetrics

open NField.Alignment
open CollisionRampEnergy CommonResetGrid DedekindReciprocity

theorem adjacent_reset_grid_bounds {N Q k : ℕ} (hQ : N^2 < Q)
    (hk2 : 2 ≤ k) (hkN : k ≤ N) :
    1 ≤ Q/k ∧ Q/k+1 < Q := by
  have hkk : k^2 ≤ N^2 := Nat.pow_le_pow_left hkN 2
  have hk : 0 < k := by omega
  have hkQ : k ≤ Q := by nlinarith
  have ha : 1 ≤ Q/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa)
  have hm := Nat.div_mul_le_self Q k
  have ha2 : 2*(Q/k) ≤ Q := (Nat.mul_le_mul_right (Q/k) hk2).trans (by simpa [mul_comm] using hm)
  exact ⟨ha, by nlinarith⟩

theorem upper_grid_quotient {N Q k j : ℕ} (hQ : N^2 < Q)
    (hk2 : 2 ≤ k) (hkN : k ≤ N) (_hj : 1 ≤ j) (hjN : j ≤ N) :
    j*(Q/k+1)/Q=j/k := by
  have hk : 0 < k := by omega
  have hQpos : 0 < Q := by omega
  have hja : j*k < Q := (Nat.mul_le_mul hjN hkN).trans_lt (by simpa [pow_two] using hQ)
  have hqle := Nat.div_mul_le_self Q k
  have hqhi : Q < (Q/k+1)*k := by simpa [mul_comm] using Nat.lt_mul_div_succ Q hk
  have hjhi : j < (j/k+1)*k := by simpa [mul_comm] using Nat.lt_mul_div_succ j hk
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hQpos).mpr
    have hstep : j*(Q/k+1)*k < (j+1)*Q := by
      nlinarith [Nat.mul_le_mul_left j hqle]
    have hlarge := Nat.mul_le_mul_right Q (show j+1 ≤ (j/k+1)*k by omega)
    nlinarith
  · apply (Nat.le_div_iff_mul_le hQpos).mpr
    have hfirst := Nat.mul_le_mul_left (j/k) hqhi.le
    have hsecond := Nat.mul_le_mul_right (Q/k+1) (Nat.div_mul_le_self j k)
    nlinarith

theorem adjacent_grid_quotient_difference {N Q k j : ℕ} (hQ : N^2 < Q)
    (hk2 : 2 ≤ k) (hkN : k ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hreturn : ¬k ∣ Q) :
    j*(Q/k)/Q+(if k ∣ j then 1 else 0)=j*(Q/k+1)/Q := by
  have hk : 0 < k := by omega
  have hQpos : 0 < Q := by omega
  have hs : 0 < Q%k := Nat.pos_of_ne_zero (by simpa only [Nat.dvd_iff_mod_eq_zero] using hreturn)
  have hsk : Q%k < k := Nat.mod_lt Q hk
  have hja : j*k < Q := (Nat.mul_le_mul hjN hkN).trans_lt (by simpa [pow_two] using hQ)
  have hjs : j*(Q%k) < Q := (Nat.mul_le_mul_left j hsk.le).trans_lt hja
  have hprod : j*(Q/k)*k+j*(Q%k)=j*Q := by
    nlinarith [congrArg (fun t : ℕ => j*t) (Nat.div_add_mod Q k)]
  rw [upper_grid_quotient hQ hk2 hkN hj hjN]
  by_cases hd : k ∣ j
  · rw [if_pos hd]
    have hm : 1 ≤ j/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using Nat.le_of_dvd hj hd)
    have hje : j/k*k=j := Nat.div_mul_cancel hd
    have hstrict : j*(Q/k) < (j/k)*Q := by
      have hpos : 0 < j*(Q%k) := Nat.mul_pos hj hs
      have he := congrArg (fun t : ℕ => t*Q) hje
      nlinarith
    have hlower : (j/k-1)*Q ≤ j*(Q/k) := by
      have he := congrArg (fun t : ℕ => t*Q) hje
      have hmQ : (j/k-1)*Q+Q=(j/k)*Q := by
        calc
          _ = (j/k-1+1)*Q := by ring
          _ = _ := by rw [Nat.sub_add_cancel hm]
      nlinarith
    have hquot_lt : j*(Q/k)/Q < j/k := (Nat.div_lt_iff_lt_mul hQpos).mpr hstrict
    have hquot_ge : j/k-1 ≤ j*(Q/k)/Q := (Nat.le_div_iff_mul_le hQpos).mpr hlower
    omega
  · rw [if_neg hd, add_zero]
    have hr : j/k*k < j := by
      have he : (j/k)*k+j%k=j := by simpa [mul_comm] using Nat.div_add_mod j k
      have hnz : j%k ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
      omega
    have hlarge := Nat.mul_le_mul_right Q (show j/k*k+1 ≤ j by omega)
    have hlower : j/k*Q ≤ j*(Q/k) := by nlinarith
    apply Nat.le_antisymm
    · calc
        _ ≤ j*(Q/k+1)/Q := Nat.div_le_div_right (Nat.mul_le_mul_left j (Nat.le_succ _))
        _ = _ := upper_grid_quotient hQ hk2 hkN hj hjN
    · exact (Nat.le_div_iff_mul_le hQpos).mpr hlower

theorem grid_numerator_remainder_ne_zero {Q j a : ℕ} (_hQ : 0 < Q)
    (hj : j.Coprime Q) (ha : 0 < a) (haQ : a < Q) : (j*a)%Q ≠ 0 := by
  intro hz
  have hd : Q ∣ j*a := Nat.dvd_of_mod_eq_zero hz
  have haD : Q ∣ a := hj.symm.dvd_of_dvd_mul_left hd
  exact Nat.not_dvd_of_pos_of_lt ha haQ haD

theorem midpoint_row_grid_quotient {Q j a : ℕ} (hQ : 0 < Q)
    (hj : j.Coprime Q) (ha : 0 < a) (haQ : a < Q) :
    midpointRow j ((a : ℝ)/(Q : ℝ)) =
      ((j : ℝ)*(a : ℝ))/(Q : ℝ)-((j*a/Q : ℕ) : ℝ)-1/2 := by
  rw [midpointRow_rational hQ]
  unfold rationalSawtooth
  rw [if_neg (grid_numerator_remainder_ne_zero hQ hj ha haQ)]
  push_cast
  have he : ((j*a%Q : ℕ) : ℝ)+((j*a/Q : ℕ) : ℝ)*(Q : ℝ)=(j : ℝ)*(a : ℝ) := by
    exact_mod_cast (show (j*a)%Q+(j*a/Q)*Q=j*a by
      simpa [mul_comm] using Nat.mod_add_div (j*a) Q)
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  field_simp
  nlinarith

end NField.ResetForests.SourceMetrics
