/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ResetGrid
import NField.Alignment.CommonResetGram
/-! # Faithfulness of the actual sampled field

Two initial readings recover the common slope and total source mass.
Each pair bracketing 1/k then recovers the literal divisor reset mass.
Triangular divisor inversion recovers every original source coefficient.
-/

noncomputable section

namespace NField.ResetForests.SourceMetrics

open scoped BigOperators
open NField.Alignment CommonResetGram

def sourceSlope (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j*(j : ℝ)

def sourceTotal (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j

def quotientReading (N Q : ℕ) (c : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j*((j*a/Q : ℕ) : ℝ)

theorem weighted_grid_quotient (N Q : ℕ) (c : ℕ → ℝ) (a : ℕ)
    (hQ : 0 < Q) (ha : 0 < a) (haQ : a < Q)
    (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) :
    weightedProfile N c ((a : ℝ)/(Q : ℝ)) =
      2*(((a : ℝ)/(Q : ℝ))*sourceSlope N c-quotientReading N Q c a-sourceTotal N c/2) := by
  unfold weightedProfile
  congr 1
  unfold sourceSlope quotientReading sourceTotal
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [midpoint_row_grid_quotient hQ (hunit j hj) ha haQ]
  ring

theorem initial_quotient_readings {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (c : ℕ → ℝ) : quotientReading N Q c 1=0 ∧ quotientReading N Q c 2=0 := by
  have h2 : 2*N < Q := by nlinarith
  constructor <;> unfold quotientReading <;> apply Finset.sum_eq_zero <;> intro j hj
  · have hjN := (Finset.mem_Icc.mp hj).2
    rw [Nat.mul_one, Nat.div_eq_of_lt (by nlinarith : j < Q), Nat.cast_zero, mul_zero]
  · have hjN := (Finset.mem_Icc.mp hj).2
    rw [Nat.div_eq_of_lt (by omega : j*2 < Q), Nat.cast_zero, mul_zero]

theorem zero_grid_initial_moments {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (c : ℕ → ℝ) (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q)
    (hz : ∀ a ∈ Finset.range Q, weightedProfile N c ((a : ℝ)/(Q : ℝ))=0) :
    sourceSlope N c=0 ∧ sourceTotal N c=0 := by
  have hQ3 : 3 ≤ Q := by nlinarith
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have h1 := weighted_grid_quotient N Q c 1 (by omega) (by norm_num) (by omega) hunit
  have h2 := weighted_grid_quotient N Q c 2 (by omega) (by norm_num) (by omega) hunit
  rw [hz 1 (Finset.mem_range.mpr (by omega)), (initial_quotient_readings hN hQ c).1] at h1
  rw [hz 2 (Finset.mem_range.mpr (by omega)), (initial_quotient_readings hN hQ c).2] at h2
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h2
  field_simp at h1 h2
  have hslope : sourceSlope N c=0 := by nlinarith
  refine ⟨hslope, ?_⟩
  have hm : (Q : ℝ)*sourceTotal N c=0 := by nlinarith
  exact (mul_eq_zero.mp hm).resolve_left hQR

theorem quotient_reset_difference {N Q k : ℕ} (hQ : N^2 < Q)
    (hk2 : 2 ≤ k) (hkN : k ≤ N) (hreturn : ¬k ∣ Q) (c : ℕ → ℝ) :
    quotientReading N Q c (Q/k+1)-quotientReading N Q c (Q/k)=Core.resetMass N c k := by
  unfold quotientReading Core.resetMass Core.sourceIndices
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hb := Finset.mem_Icc.mp hj
  have he := adjacent_grid_quotient_difference hQ hk2 hkN hb.1 hb.2 hreturn
  by_cases hd : k ∣ j
  · simp only [hd, if_true] at he ⊢
    have hr : ((j*(Q/k)/Q : ℕ) : ℝ)+1=((j*(Q/k+1)/Q : ℕ) : ℝ) := by exact_mod_cast he
    rw [← hr]
    ring
  · simp only [hd, if_false, add_zero] at he ⊢
    rw [← he]
    ring

theorem sampled_field_injective {N Q : ℕ} (hN : 2 ≤ N) (hQ : N^2 < Q)
    (c : ℕ → ℝ) (hunit : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q)
    (hz : ∀ a ∈ Finset.range Q, weightedProfile N c ((a : ℝ)/(Q : ℝ))=0) :
    ∀ j ∈ Finset.Icc 1 N, c j=0 := by
  have hm := zero_grid_initial_moments hN hQ c hunit hz
  have hmass : ∀ k ∈ Finset.Icc 1 N, Core.resetMass N c k=0 := by
    intro k hk
    have hkI := Finset.mem_Icc.mp hk
    by_cases hk1 : k=1
    · subst k
      simpa [Core.resetMass, Core.sourceIndices, sourceTotal] using hm.2
    · have hk2 : 2 ≤ k := by omega
      have hb := adjacent_reset_grid_bounds hQ hk2 hkI.2
      have hreturn : ¬k ∣ Q := by
        intro hd
        have := (hunit k hk).gcd_eq_one
        rw [Nat.gcd_eq_left hd] at this
        omega
      have hlow := weighted_grid_quotient N Q c (Q/k) (by omega) hb.1 (by omega) hunit
      have hupp := weighted_grid_quotient N Q c (Q/k+1) (by omega) (by omega) hb.2 hunit
      rw [hz _ (Finset.mem_range.mpr (by omega)), hm.1, hm.2] at hlow
      rw [hz _ (Finset.mem_range.mpr hb.2), hm.1, hm.2] at hupp
      have he := quotient_reset_difference hQ hk2 hkI.2 hreturn c
      linarith
  apply Core.reset_mass_injective N (e := fun _ => 0)
  intro k hk
  rw [hmass k hk]
  simp [Core.resetMass]

theorem prime_square_source_units {p j : ℕ} (hp : p.Prime)
    (hj : j ∈ Finset.Icc 1 (p-1)) : j.Coprime (p^2) := by
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  have hb := Finset.mem_Icc.mp hj
  exact Nat.not_dvd_of_pos_of_lt hb.1 (by have := hp.two_le; omega)

theorem prime_square_field_injective {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (c : ℕ → ℝ)
    (hz : ∀ a ∈ Finset.range (p^2), weightedProfile (p-1) c ((a : ℝ)/(p : ℝ)^2)=0) :
    ∀ j ∈ Finset.Icc 1 (p-1), c j=0 := by
  have hN : 2 ≤ p-1 := by have := hp.two_le; omega
  apply sampled_field_injective hN (by nlinarith [Nat.sub_add_cancel hp.one_le]) c
    (fun j hj => prime_square_source_units hp hj)
  simpa only [Nat.cast_pow] using hz

end NField.ResetForests.SourceMetrics
