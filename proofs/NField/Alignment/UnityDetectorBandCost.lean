/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityPrescribedDetectors

/-! # The literal two-parity detector band budget -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityDetectorBandCost
open scoped BigOperators
open UnityNativeHilbert UnityNativeProjection UnityNativeIsometry UnityProjectionBands
open UnityPrescribedDetectors

theorem coarseCutoff_le (N h : ℕ) : coarseCutoff N h≤N := Nat.div_le_self _ _

theorem coarseCutoff_antitone (N : ℕ) : Antitone (coarseCutoff N) := by
  intro h k hhk
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) hhk) (by positivity)

/-- Title: `Two additional depths divide the coarse cutoff by four`. -/
theorem coarseCutoff_two (N h : ℕ) : coarseCutoff N (h+2)=coarseCutoff N h/4 := by
  simp [coarseCutoff, pow_add, Nat.div_div_eq_div_mul]

theorem coarseCutoff_two_le (N h : ℕ) : 4*coarseCutoff N (h+2)≤coarseCutoff N h := by
  rw [coarseCutoff_two]
  exact Nat.mul_div_le _ _

/-- The exact pre-conditioning detector cost at one depth. -/
def bandCost (N h : ℕ) : ℝ := ‖newRoot (coarseCutoff N h)‖^2

theorem bandCost_nonneg (N h : ℕ) : 0≤bandCost N h := sq_nonneg _

def leadingEnergy (N : ℕ) : ℝ := projectedEnergy rootDetail (4*N)

def majorant (N h : ℕ) : ℝ :=
  if h<2 then leadingEnergy N else projectedEnergy rootDetail (coarseCutoff N (h-2))

theorem majorant_nonneg (N h : ℕ) : 0≤majorant N h := by
  unfold majorant leadingEnergy
  split_ifs <;> exact projectedEnergy_nonneg _ _

theorem bandCost_two_step (N h : ℕ) : bandCost N h≤majorant N h-majorant N (h+2) := by
  have h2 : ¬h+2<2 := by omega
  rw [bandCost, newRoot, band_energy, majorant, majorant, if_neg h2]
  simp only [Nat.add_sub_cancel]
  apply sub_le_sub_right
  split_ifs with hh
  · exact projectedEnergy_mono rootDetail (Nat.mul_le_mul_left 4 (coarseCutoff_le N h))
  · have he : h-2+2=h := by omega
    have hc := coarseCutoff_two_le N (h-2)
    rw [he] at hc
    exact projectedEnergy_mono rootDetail hc

/-- Finite two-step telescoping retains both boundary terms. -/
theorem sum_two_step (c a : ℕ → ℝ) (hc : ∀h, c h≤a h-a (h+2)) (H : ℕ) :
    (∑ h ∈ Finset.range H, c h)≤a 0+a 1-a H-a (H+1) := by
  induction H with
  | zero => simp only [Finset.sum_range_zero, Nat.zero_add]; linarith
  | succ H ih =>
    rw [Finset.sum_range_succ]
    have h := hc H
    have he : H+1+1=H+2 := by omega
    rw [he]
    linarith

/-- Title: `The two-parity band budget retains both boundary energies`.

 The exact two-parity budget before dropping its two final energies. -/
theorem full_band_cost_bound (N H : ℕ) :
    (∑ h ∈ Finset.range H, bandCost N h) ≤
      2*leadingEnergy N-majorant N H-majorant N (H+1) := by
  have h := sum_two_step (bandCost N) (majorant N) (bandCost_two_step N) H
  simpa [majorant, two_mul] using h

theorem full_band_cost_le_two (N H : ℕ) : (∑ h ∈ Finset.range H, bandCost N h)≤2 := by
  have h := full_band_cost_bound N H
  have hA : leadingEnergy N≤1 := by
    simpa only [leadingEnergy, rootDetail_norm_sq] using projectedEnergy_le rootDetail (4*N)
  nlinarith [majorant_nonneg N H, majorant_nonneg N (H+1)]

/-- The same bound holds for any finite selection of depths. -/
theorem selected_band_cost_le_two (N : ℕ) (S : Finset ℕ) : (∑ h∈S, bandCost N h)≤2 := by
  classical
  obtain ⟨H,hH⟩ := Finset.exists_nat_subset_range S
  apply le_trans _ (full_band_cost_le_two N H)
  exact Finset.sum_le_sum_of_subset_of_nonneg hH (fun h _ _ => bandCost_nonneg N h)

/-- The least coarse cutoff in a finite nonempty selection is at its greatest depth. -/
def minimumCutoff (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) : ℕ := coarseCutoff N (S.max' hS)

theorem minimumCutoff_le (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) {h : ℕ} (hh : h∈S) :
    minimumCutoff N S hS≤coarseCutoff N h :=
  coarseCutoff_antitone N (Finset.le_max' S h hh)

theorem minimumCutoff_mem (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    minimumCutoff N S hS∈S.image (coarseCutoff N) :=
  Finset.mem_image.mpr ⟨S.max' hS, Finset.max'_mem S hS, rfl⟩

theorem majorant_at_last (N k : ℕ) :
    projectedEnergy rootDetail (coarseCutoff N k)≤majorant N (k+1) := by
  unfold majorant
  split_ifs with h
  · exact projectedEnergy_mono rootDetail ((coarseCutoff_le N k).trans (by omega))
  · exact projectedEnergy_mono rootDetail (coarseCutoff_antitone N (by omega))

/-- Title: `Selected band cost retains the least coarse cutoff`.

 The sharper literal band budget retains the least selected coarse cutoff. -/
theorem selected_band_cost_sharp (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    (∑ h∈S, bandCost N h)≤2*(projectedEnergy rootDetail (4*N)-
      projectedEnergy rootDetail (minimumCutoff N S hS)) := by
  have hsub : S⊆Finset.range (S.max' hS+1) := by
    intro h hh
    exact Finset.mem_range.mpr (by have := Finset.le_max' S h hh; omega)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => bandCost_nonneg N h)
  have hb := full_band_cost_bound N (S.max' hS+1)
  have hm := majorant_at_last N (S.max' hS)
  have he : majorant N (S.max' hS+1+1) = projectedEnergy rootDetail (minimumCutoff N S hS) := by
    unfold majorant minimumCutoff
    rw [if_neg (by omega)]
    congr 2
  rw [he] at hb
  unfold minimumCutoff leadingEnergy at *
  linarith

/-- The paper's actual total eligible detector cost. -/
def totalCost (N : ℕ) : ℝ := ∑ h∈eligible N, bandCost N h

theorem totalCost_nonneg (N : ℕ) : 0≤totalCost N :=
  Finset.sum_nonneg (fun h _ => bandCost_nonneg N h)

/-- Title: `The complete prescribed detector cost is at most two`. -/
theorem totalCost_le_two (N : ℕ) : totalCost N≤2 := selected_band_cost_le_two N (eligible N)

/-- Title: `The prescribed cost has the sharper projection-energy bound`. -/
theorem totalCost_sharp (N : ℕ) (hI : (eligible N).Nonempty) :
    totalCost N≤2*(projectedEnergy rootDetail (4*N)-
      projectedEnergy rootDetail (minimumCutoff N (eligible N) hI)) :=
  selected_band_cost_sharp N (eligible N) hI

end NField.Alignment.UnityDetectorBandCost
