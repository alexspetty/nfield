/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseTraces
import NField.Alignment.CommonResetHuxley
/-! # Matching the complete shifted-grid and reduced-reset jump sums -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PhaseIdentity

open scoped BigOperators Topology
open Filter Set NField.Alignment
open CommonResetGram CommonResetWeightedSources CommonResetHuxley
open SourceMetrics FibreReconstruction FibreTraces ShiftedEnergy

theorem weighted_reduced_grid_sum (N : ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : f 0=0) :
    (∑ j ∈ Finset.Icc 1 N, c j*∑ a ∈ Finset.range j, f ((a : ℝ)/j))=
      ∑ d ∈ Finset.Icc 2 N, resetWeight N c d*∑ a ∈ resetAddresses d, f ((a : ℝ)/d) := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*
        ∑ a ∈ (Finset.range d).filter (fun a => a.Coprime d), f ((a : ℝ)/d) := by
      rw [← weighted_divisor_columns]
      apply Finset.sum_congr rfl
      intro j hj
      rw [reduced_grid_sum (Finset.mem_Icc.mp hj).1 f]
    _ = ∑ d ∈ Finset.Icc 2 N, resetWeight N c d*
        ∑ a ∈ (Finset.range d).filter (fun a => a.Coprime d), f ((a : ℝ)/d) := by
      symm
      apply CommonResetDedekind.sum_Icc_remove_one
      simp [hf]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hs : (Finset.range d).filter (fun a => a.Coprime d)=resetAddresses d := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, resetAddresses, Finset.mem_Ico]
        have hdz : d≠1 := by have := (Finset.mem_Icc.mp hd).1; omega
        constructor
        · rintro ⟨ha,hc⟩
          have haz : a≠0 := by intro he; subst a; exact hdz (by simpa using hc)
          exact ⟨⟨by omega,ha⟩,hc⟩
        · rintro ⟨⟨_,ha⟩,hc⟩
          exact ⟨ha,hc⟩
      rw [hs]

theorem grid_contact_exists {j : ℕ} (hj : 0<j) {x : ℝ} (hx : x ∈ Ico 0 1) :
    Int.fract ((j : ℝ)*x)=0 ↔ ∃ a ∈ Finset.range j, (a : ℝ)/(j : ℝ)=x := by
  constructor
  · intro h
    have hfloor : (Int.floor ((j : ℝ)*x) : ℝ)=(j : ℝ)*x := by
      unfold Int.fract at h
      linarith
    have hn : 0≤Int.floor ((j : ℝ)*x) := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hx.1)
    refine ⟨(Int.floor ((j : ℝ)*x)).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hcast : ((Int.floor ((j : ℝ)*x)).toNat : ℝ)=(j : ℝ)*x := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, hfloor]
      have hlt : ((Int.floor ((j : ℝ)*x)).toNat : ℝ)<j := by
        rw [hcast]
        exact mul_lt_of_lt_one_right (by exact_mod_cast hj) hx.2
      exact_mod_cast hlt
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg hn,hfloor]
      exact mul_div_cancel_left₀ x (by exact_mod_cast hj.ne')
  · rintro ⟨a,_,ha⟩
    rw [← ha, mul_div_cancel₀ _ (by exact_mod_cast hj.ne')]
    exact Int.fract_natCast a

theorem grid_point_sum {j : ℕ} (hj : 0<j) {x : ℝ} (hx : x ∈ Ico 0 1) (w : ℝ → ℝ) :
    (∑ a ∈ Finset.range j, if (a : ℝ)/j=x then w ((a : ℝ)/j) else 0)=
      if Int.fract ((j : ℝ)*x)=0 then w x else 0 := by
  classical
  by_cases hc : Int.fract ((j : ℝ)*x)=0
  · obtain ⟨a,ha,hax⟩ := (grid_contact_exists hj hx).mp hc
    rw [if_pos hc]
    rw [Finset.sum_eq_single a]
    · simp [hax]
    · intro b _ hba
      apply if_neg
      intro he
      have hcast := (div_left_inj' (by exact_mod_cast hj.ne' : (j : ℝ)≠0)).mp (he.trans hax.symm)
      exact hba (by exact_mod_cast hcast)
    · exact fun h => (h ha).elim
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a ha
    exact if_neg (fun h => hc ((grid_contact_exists hj hx).mpr ⟨a,ha,h⟩))

theorem point_contact_decomposition (N : ℕ) (c : ℕ → ℝ) {x : ℝ}
    (hx : x ∈ Ioo 0 1) (w : ℝ → ℝ) :
    contactMass N c x*w x=
      ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        if (a : ℝ)/d=x then resetWeight N c d*w ((a : ℝ)/d) else 0 := by
  calc
    _ = ∑ j ∈ Finset.Icc 1 N, c j*
        ∑ a ∈ Finset.range j, if (a : ℝ)/j=x then w ((a : ℝ)/j) else 0 := by
      unfold contactMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [grid_point_sum (Finset.mem_Icc.mp hj).1 ⟨hx.1.le,hx.2⟩]
      split_ifs <;> ring
    _ = _ := by
      rw [weighted_reduced_grid_sum N c (fun t => if t=x then w t else 0)
        (by simp [ne_of_lt hx.1])]
      simp only [Finset.mul_sum, mul_ite, mul_zero]

theorem fibre_point_exists {Q : ℕ} (hQ : 0<Q) {t ρ : ℝ}
    (ht : t ∈ Ico 0 1) (hρ : ρ ∈ Ico 0 1) :
    Int.fract ((Q : ℝ)*t)=ρ ↔ ∃ v : Fin Q, t=((v.val : ℝ)+ρ)/(Q : ℝ) := by
  have hQR : (0 : ℝ)<Q := by exact_mod_cast hQ
  constructor
  · intro h
    have hn : 0≤Int.floor ((Q : ℝ)*t) := Int.floor_nonneg.mpr (mul_nonneg hQR.le ht.1)
    have hfloor : ((Int.floor ((Q : ℝ)*t)).toNat : ℝ)=(Q : ℝ)*t-ρ := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
      unfold Int.fract at h
      linarith
    have hb : (Int.floor ((Q : ℝ)*t)).toNat<Q := by
      have hlt : ((Int.floor ((Q : ℝ)*t)).toNat : ℝ)<Q := by
        rw [hfloor]
        have := mul_lt_of_lt_one_right hQR ht.2
        linarith [hρ.1]
      exact_mod_cast hlt
    refine ⟨⟨_,hb⟩, ?_⟩
    dsimp only
    rw [hfloor]
    field_simp
    ring
  · rintro ⟨v,hv⟩
    apply Int.fract_eq_iff.mpr ⟨hρ.1,hρ.2,(v.val : ℤ),?_⟩
    rw [hv]
    push_cast
    field_simp
    ring

theorem fibre_point_sum {Q : ℕ} (hQ : 0<Q) {t ρ : ℝ}
    (ht : t ∈ Ico 0 1) (hρ : ρ ∈ Ico 0 1) (w : ℝ) :
    (∑ v : Fin Q, if t=((v.val : ℝ)+ρ)/(Q : ℝ) then w else 0)=
      if Int.fract ((Q : ℝ)*t)=ρ then w else 0 := by
  classical
  by_cases he : Int.fract ((Q : ℝ)*t)=ρ
  · obtain ⟨v,hv⟩ := (fibre_point_exists hQ ht hρ).mp he
    rw [if_pos he, Finset.sum_eq_single v]
    · simp [hv]
    · intro u _ huv
      apply if_neg
      intro hu
      have hcast := (div_left_inj' (by exact_mod_cast hQ.ne' : (Q : ℝ)≠0)).mp
        (hu.symm.trans hv)
      apply huv
      apply Fin.ext
      exact_mod_cast add_right_cancel hcast
    · simp
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (fun hv => he ((fibre_point_exists hQ ht hρ).mpr ⟨v,hv⟩))

theorem shifted_point_in_unit_interval {Q : ℕ} (hQ : 0<Q) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 1) (v : Fin Q) : ((v.val : ℝ)+ρ)/(Q : ℝ) ∈ Ioo 0 1 := by
  have hQR : (0 : ℝ)<Q := by exact_mod_cast hQ
  constructor
  · apply div_pos _ hQR
    linarith [show (0 : ℝ)≤v.val from Nat.cast_nonneg _,hρ.1]
  · rw [div_lt_one hQR]
    have hb : (v.val : ℝ)+1≤Q := by exact_mod_cast v.isLt
    linarith [hρ.2]

theorem shifted_contact_events {Q : ℕ} (hQ : 0<Q) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 1)
    (N : ℕ) (c : ℕ → ℝ) (w : ℝ → ℝ) :
    (∑ v : Fin Q, contactMass N c (((v.val : ℝ)+ρ)/(Q : ℝ))*
      w (((v.val : ℝ)+ρ)/(Q : ℝ)))=
      ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        if resetPhase Q d a=ρ then resetWeight N c d*w ((a : ℝ)/d) else 0 := by
  calc
    _ = ∑ v : Fin Q, ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ resetAddresses d,
        if (a : ℝ)/d=((v.val : ℝ)+ρ)/(Q : ℝ) then
          resetWeight N c d*w ((a : ℝ)/d) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact point_contact_decomposition N c (shifted_point_in_unit_interval hQ hρ v) w
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ha0,had,_⟩ := reset_address_bounds ha
      have hdR : (0 : ℝ)<d := by exact_mod_cast (by omega : 0<d)
      exact fibre_point_sum hQ
        ⟨div_nonneg (Nat.cast_nonneg _) hdR.le,(div_lt_one hdR).mpr (by exact_mod_cast had)⟩
        ⟨hρ.1.le,hρ.2⟩ _

/-- Title: `The full shifted-grid jump is exactly the full reduced-reset phase jump`. -/
theorem shifted_jump_matches_phase {Q : ℕ} (hQ : 0<Q) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 1)
    (N : ℕ) (c : ℕ → ℝ) :
    shiftedRightSum N Q c ρ-shiftedLeftSum N Q c ρ=
      phaseJumpProfile N Q c ρ-phaseLeftSum N Q c ρ := by
  rw [shifted_sum_jump,phase_jump_size]
  convert shifted_contact_events hQ hρ N c (fun x => -4*weightedProfile N c x) using 1
  · apply Finset.sum_congr rfl
    intro v _
    ring
  · apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro a _
    by_cases he : resetPhase Q d a=ρ
    · simp only [if_pos he,squaredResetJump]
      ring
    · simp only [if_neg he]

end NField.ResetForests.PhaseIdentity
