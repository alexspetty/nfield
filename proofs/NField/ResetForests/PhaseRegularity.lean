/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseMatching
import NField.ResetForests.PhaseRight
/-! # The printed phase exclusion and the original source's regular points -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PhaseIdentity

open scoped BigOperators Topology
open Filter Set MeasureTheory NField.Alignment
open CommonResetGram CommonResetWeightedSources FibreTraces ShiftedEnergy

theorem regular_iff_unit_contact_zero (N : ℕ) (x : ℝ) :
    regularAt N x ↔ contactMass N (fun _ => 1) x=0 := by
  constructor
  · intro h
    exact Finset.sum_eq_zero (fun j hj => if_neg (h j hj))
  · intro h j hj hz
    have hn (k : ℕ) (_ : k ∈ Finset.Icc 1 N) :
        (0 : ℝ) ≤ (if Int.fract ((k : ℝ)*x)=0 then 1 else 0) := by split_ifs <;> norm_num
    have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp h j hj
    norm_num [hz] at he

theorem phase_denominator_contact {d : ℕ} (hd : 0<d) (Q a : ℕ) :
    Int.fract ((d : ℝ)*resetPhase Q d a)=0 := by
  apply Int.fract_eq_zero_iff.mpr
  refine ⟨(Q*a : ℕ)-(d : ℤ)*Int.floor ((Q : ℝ)*((a : ℝ)/d)),?_⟩
  simp only [resetPhase,Int.fract,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd.ne'
  field_simp

theorem regular_excludes_phases {N : ℕ} {ρ : ℝ} (hρ : regularAt N ρ) (Q : ℕ) :
    ∀ d ∈ Finset.Icc 2 N, ∀ a ∈ resetAddresses d, resetPhase Q d a≠ρ := by
  intro d hd a _ he
  have hd1 : d ∈ Finset.Icc 1 N := by
    have := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega,this.2⟩
  exact hρ d hd1 (he ▸ phase_denominator_contact (Finset.mem_Icc.mp hd1).1 Q a)

/-- Title: `Excluding every reset phase is equivalent to regularity of the original source`. -/
theorem phase_exclusion_iff_regular {N Q : ℕ} (hQ : 0<Q)
    (hc : ∀ j ∈ Finset.Icc 1 N, j.Coprime Q) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 1) :
    (∀ d ∈ Finset.Icc 2 N, ∀ a ∈ resetAddresses d, resetPhase Q d a≠ρ) ↔ regularAt N ρ := by
  constructor
  · intro he
    apply (regular_iff_unit_contact_zero N ρ).mpr
    have hs := shifted_contact_events hQ hρ N (fun _ => 1) (fun _ => 1)
    simp only [mul_one,contact_coprime_distribution hQ hc] at hs
    rw [hs]
    apply Finset.sum_eq_zero
    intro d hd
    exact Finset.sum_eq_zero (fun a ha => if_neg (he d hd a ha))
  · exact fun h => regular_excludes_phases h Q

theorem regular_ae (N : ℕ) : ∀ᵐ x ∂volume, regularAt N x := by
  filter_upwards [contact_ae_zero N (fun _ => 1)] with x hx
  exact (regular_iff_unit_contact_zero N x).mpr hx

theorem contact_zero_at_regular {N : ℕ} {x : ℝ} (hx : regularAt N x) (c : ℕ → ℝ) :
    contactMass N c x=0 := Finset.sum_eq_zero (fun j hj => if_neg (hx j hj))

theorem shifted_right_eq_midpoint {N Q : ℕ} (hQ : 0<Q) {ρ : ℝ}
    (hρ : regularAt N ρ) (c : ℕ → ℝ) :
    shiftedRightSum N Q c ρ=shiftedEnergySum N Q c ρ := by
  apply Finset.sum_congr rfl
  intro a _
  rw [profileRight,contact_zero_at_regular (regular_at_fibre hQ ρ a.val hρ),sub_zero]

end NField.ResetForests.PhaseIdentity
