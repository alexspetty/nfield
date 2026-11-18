/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseCells
import NField.ResetForests.Sampling
/-! # The complete centered-cell fringe

Every excluded clock belongs to an excluded centered phase. Both end cells
and the full original source reading are retained before normalization.
-/

noncomputable section

namespace NField.ResetForests.PhasePopulations

open scoped BigOperators
open NField.Alignment
open CenteredPhase DedekindFourierMoment CommonResetSampling

def phaseReturnCutoff (p : ℕ) : ℕ := min (Nat.sqrt p) (p/3)

def retainedPhase (p h : ℕ) : Prop :=
  phaseReturnCutoff p+2 ≤ h ∧ h ≤ p/3-1

instance retainedPhaseDecidable (p h : ℕ) : Decidable (retainedPhase p h) :=
  inferInstanceAs (Decidable (_ ∧ _))

def phaseFringeCells (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p/3)).filter (fun h => ¬retainedPhase p h)

def phaseFringeWork (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (p-1),
    if retainedPhase p (centeredPhase p k) then 0 else |4*Core.clockReading (p-1) (p^2) k|

def retainedMask (p k : ℕ) : Bool := decide (retainedPhase p (centeredPhase p k))

def retainedClocks (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p-1)).filter (fun k => retainedPhase p (centeredPhase p k))

def retainedReading (p : ℕ) : ℝ :=
  4*Core.selectedReading (p-1) (p^2) (retainedMask p)/(p : ℝ)^2

theorem phase_fringe_card (p : ℕ) :
    (phaseFringeCells p).card ≤ phaseReturnCutoff p+2 := by
  have hsub : phaseFringeCells p ⊆ Finset.Icc 1 (phaseReturnCutoff p+1) ∪ {p/3} := by
    intro h hh
    obtain ⟨hI, hnot⟩ := Finset.mem_filter.mp hh
    simp only [Finset.mem_Icc] at hI
    simp only [retainedPhase, not_and_or, not_le] at hnot
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
    omega
  calc
    _ ≤ (Finset.Icc 1 (phaseReturnCutoff p+1) ∪ {p/3}).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (phaseReturnCutoff p+1)).card+({p/3} : Finset ℕ).card :=
      Finset.card_union_le _ _
    _ = _ := by simp

theorem phase_fringe_card_sqrt {p : ℕ} (hp : 1 ≤ p) :
    ((phaseFringeCells p).card : ℝ) ≤ 3*Real.sqrt (p : ℝ) := by
  have hcard : ((phaseFringeCells p).card : ℝ) ≤ (phaseReturnCutoff p : ℝ)+2 := by
    exact_mod_cast phase_fringe_card p
  have hR : (phaseReturnCutoff p : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have hn : phaseReturnCutoff p ≤ Nat.sqrt p := min_le_left _ _
    exact (Nat.cast_le.mpr hn).trans Real.nat_sqrt_le_real_sqrt
  have hs : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hp)
  linarith

theorem sum_phase_work (p : ℕ) (cells : Finset ℕ) :
    (∑ h ∈ cells, phaseWork p h) =
      ∑ k ∈ Finset.Icc 2 (p-1),
        if centeredPhase p k ∈ cells then |4*Core.clockReading (p-1) (p^2) k| else 0 := by
  unfold phaseWork phaseClocks
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]

theorem phase_fringe_partition {p : ℕ} (hp : p.Prime) :
    phaseFringeWork p=∑ h ∈ phaseFringeCells p, phaseWork p h := by
  rw [sum_phase_work]
  unfold phaseFringeWork
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk2, hkpN⟩ := Finset.mem_Icc.mp hk
  have hr := centered_phase_range hp hk2 (by omega : k < p)
  have he : centeredPhase p k ∈ phaseFringeCells p ↔ ¬retainedPhase p (centeredPhase p k) := by
    simp only [phaseFringeCells, Finset.mem_filter, Finset.mem_Icc, hr.1, hr.2, and_self, true_and]
  by_cases hs : retainedPhase p (centeredPhase p k) <;> simp [he, hs]

theorem phase_fringe_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      phaseFringeWork p ≤ C*(p : ℝ)^(3/2+ε) := by
  obtain ⟨C, hC, hc⟩ := phase_work_small_power ε hε
  refine ⟨3*C, by positivity, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [phase_fringe_partition hp]
  calc
    _ ≤ ∑ _h ∈ phaseFringeCells p, C*(p : ℝ)^(1+ε) :=
      Finset.sum_le_sum (fun h _ => hc p hp h)
    _ = ((phaseFringeCells p).card : ℝ)*(C*(p : ℝ)^(1+ε)) := by simp
    _ ≤ (3*Real.sqrt (p : ℝ))*(C*(p : ℝ)^(1+ε)) :=
      mul_le_mul_of_nonneg_right (phase_fringe_card_sqrt hp.one_le) (by positivity)
    _ = (3*C)*((p : ℝ)^(1/2 : ℝ)*(p : ℝ)^(1+ε)) := by rw [Real.sqrt_eq_rpow]; ring
    _ = _ := by
      rw [← Real.rpow_add hpR]
      congr 2
      ring

theorem retained_work_sum (p : ℕ) :
    (∑ k ∈ retainedClocks p, 4*Core.clockReading (p-1) (p^2) k) =
      4*Core.selectedReading (p-1) (p^2) (retainedMask p) := by
  unfold retainedClocks Core.selectedReading retainedMask
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hs : retainedPhase p (centeredPhase p k) <;> simp [hs]

theorem complement_reading_abs_le (p : ℕ) :
    |4*Core.selectedReading (p-1) (p^2) (fun k => !(retainedMask p k))| ≤ phaseFringeWork p := by
  unfold Core.selectedReading phaseFringeWork
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 (p-1),
        |4*(if !(retainedMask p k) then Core.clockReading (p-1) (p^2) k else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hs : retainedPhase p (centeredPhase p k) <;> simp [retainedMask, hs]

theorem harmonic_le_nat_from_mathlib (n : ℕ) : (harmonic n : ℝ) ≤ (n : ℝ) := by
  by_cases hn : n=0
  · simp [hn]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hh := harmonic_le_one_add_log n
    have hl := Real.log_le_sub_one_of_pos hnR
    linarith

theorem smooth_correction_bound {p : ℕ} (hp : 1 ≤ p) :
    |-2/(p : ℝ)+1/(p : ℝ)^2-
      ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)| ≤ 4/(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hN : ((p-1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hH : (harmonic (p-1) : ℝ) ≤ p := (harmonic_le_nat_from_mathlib _).trans hN
  have hc0 : 0 ≤ ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) := by positivity
  have hc : ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3) ≤ 1/(p : ℝ) := by
    calc
      _ ≤ ((p : ℝ)*(p : ℝ))/(3*(p : ℝ)^3) := by
        exact div_le_div_of_nonneg_right (mul_le_mul hN hH hH0 hpR.le) (by positivity)
      _ = (1/3)/(p : ℝ) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hpR.le
  have hinv : 1/(p : ℝ)^2 ≤ 1/(p : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hpR (by nlinarith)
  have hn0 : 0 ≤ 1/(p : ℝ)^2 := by positivity
  have h10 : 0 ≤ 1/(p : ℝ) := by positivity
  rw [abs_le]
  rw [show -2/(p : ℝ)=-2*(1/(p : ℝ)) by ring,
    show 4/(p : ℝ)=4*(1/(p : ℝ)) by ring]
  constructor <;> linarith

theorem retained_remainder_identity {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    defect (p-1) (p^2)-1-retainedReading p =
      4*Core.selectedReading (p-1) (p^2) (fun k => !(retainedMask p k))/(p : ℝ)^2 +
      (-2/(p : ℝ)+1/(p : ℝ)^2-
        ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)) := by
  have h := Core.prime_square_forest_decomposition hp hodd (retainedMask p)
  unfold retainedReading
  linear_combination h

theorem retained_remainder_finite_bound {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    |defect (p-1) (p^2)-1-retainedReading p| ≤
      phaseFringeWork p/(p : ℝ)^2+4/(p : ℝ) := by
  rw [retained_remainder_identity hp hodd]
  calc
    _ ≤ |4*Core.selectedReading (p-1) (p^2) (fun k => !(retainedMask p k))/(p : ℝ)^2| +
        |-2/(p : ℝ)+1/(p : ℝ)^2-
          ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)| := abs_add_le _ _
    _ ≤ _ := by
      apply add_le_add _ (smooth_correction_bound hp.one_le)
      rw [abs_div, abs_of_nonneg (sq_nonneg (p : ℝ))]
      exact div_le_div_of_nonneg_right (complement_reading_abs_le p) (sq_nonneg _)

/-- Every excluded cell is included in the printed normalized half-power allowance. -/
theorem complete_clock_interior_half_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |defect (p-1) (p^2)-1-
        (1/(p : ℝ)^2)*(∑ k ∈ retainedClocks p, 4*Core.clockReading (p-1) (p^2) k)| ≤
          C*(p : ℝ)^(-1/2+ε) := by
  obtain ⟨C, hC, hc⟩ := phase_fringe_small_power ε hε
  refine ⟨C+4, by positivity, ?_⟩
  intro p hp hodd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hinv : 1/(p : ℝ) ≤ (p : ℝ)^(-1/2+ε) := by
    calc
      _ = (p : ℝ)^(-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rw [retained_work_sum]
  have he : (1/(p : ℝ)^2)*(4*Core.selectedReading (p-1) (p^2) (retainedMask p))=
      retainedReading p := by unfold retainedReading; ring
  rw [he]
  calc
    _ ≤ phaseFringeWork p/(p : ℝ)^2+4/(p : ℝ) := retained_remainder_finite_bound hp hodd
    _ ≤ (C*(p : ℝ)^(3/2+ε))/(p : ℝ)^2+4/(p : ℝ) := by
      exact add_le_add (div_le_div_of_nonneg_right (hc p hp) (sq_nonneg (p : ℝ))) (le_refl _)
    _ = C*(p : ℝ)^(-1/2+ε)+4/(p : ℝ) := by
      rw [mul_div_assoc, ← Real.rpow_two, ← Real.rpow_sub hpR]
      rw [show (3/2+ε : ℝ)-2=-1/2+ε by ring]
    _ ≤ C*(p : ℝ)^(-1/2+ε)+4*(p : ℝ)^(-1/2+ε) := by
      apply add_le_add (le_refl _)
      calc
        4/(p : ℝ)=4*(1/(p : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

end NField.ResetForests.PhasePopulations
