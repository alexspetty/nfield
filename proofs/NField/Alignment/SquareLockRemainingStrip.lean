/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SquareLockCutoffLimits

/-! # The remaining carriers and the number of positive floor levels -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockRemainingStrip
open scoped Topology
open Filter SquareLockCarrierMass LiveCarrierDamping

theorem centered_residue_half (n k : ℕ) (hk : 0 < k) :
    2*(centeredNaturalResidue n k).natAbs ≤ k := by
  have hr : n%k < k := Nat.mod_lt n hk
  unfold centeredNaturalResidue
  dsimp only
  split_ifs with h
  · simpa only [Int.natAbs_natCast] using h
  · have hneg : ((n%k : ℕ) : ℤ)-(k : ℤ) ≤ 0 := by omega
    have hcast : (2 : ℤ)*|((n%k : ℕ) : ℤ)-(k : ℤ)| ≤ (k : ℤ) := by
      rw [abs_of_nonpos hneg]
      omega
    rw [← Int.natCast_natAbs] at hcast
    exact_mod_cast hcast

/-- Title: `The surviving carriers lie beyond twice the cutoff`. -/
theorem remaining_carrier_strip {p k : ℕ} (hk : k ∈ liveCarrierSet p) :
    2*coefficientSquareLockCutoff p < k ∧
      coefficientSquareLockCutoff p < (centeredNaturalResidue (p^2) k).natAbs := by
  have hc : coefficientSquareLockCutoff p < (centeredNaturalResidue (p^2) k).natAbs :=
    (Finset.mem_filter.mp hk).2
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  exact ⟨by have := centered_residue_half (p^2) k (by omega); omega, hc⟩

def positiveFloorValues (p k : ℕ) : Finset ℕ :=
  ((Finset.Icc (k+1) (p-1)).image (fun a => (p-1)/a)).erase 0

theorem positiveFloorValues_card_le (p k : ℕ) :
    (positiveFloorValues p k).card ≤ (p-1)/(k+1) := by
  have hsub : positiveFloorValues p k ⊆ Finset.Icc 1 ((p-1)/(k+1)) := by
    intro h hh
    obtain ⟨hne, hh⟩ := Finset.mem_erase.mp hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    have haK := (Finset.mem_Icc.mp ha).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Finset.mem_Icc.mp ha).2 (by omega),
      Nat.div_le_div_left haK (by omega)⟩
  simpa using Finset.card_le_card hsub

theorem coefficient_cutoff_lower_eventually :
    ∀ᶠ p : ℕ in atTop, (p : ℝ)/Real.log p^2 ≤ 2*(coefficientSquareLockCutoff p : ℝ) := by
  have hs := (Real.isLittleO_pow_log_id_atTop (n := 2)).natCast_atTop.bound
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hs,eventually_ge_atTop (2 : ℕ)] with p hs hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hsmall : Real.log (p : ℝ)^2 ≤ (1/2 : ℝ)*p := by
    simpa only [Function.comp_apply, id_eq, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg hpR.le] using hs
  have htwo : (2 : ℝ) ≤ (p : ℝ)/Real.log p^2 :=
    (le_div_iff₀ (sq_pos_of_pos hl)).mpr (by linarith)
  have hone : 1 ≤ coefficientSquareLockCutoff p := Nat.le_floor (by norm_num; linarith)
  have honeR : (1 : ℝ) ≤ coefficientSquareLockCutoff p := by exact_mod_cast hone
  have hf := Nat.lt_floor_add_one ((p : ℝ)/Real.log p^2)
  change (p : ℝ)/Real.log p^2 < (coefficientSquareLockCutoff p : ℝ)+1 at hf
  linarith

/-- Title: `Quadratic logarithmic bound for the remaining floor levels`. -/
theorem remaining_floor_levels :
    ∀ᶠ p : ℕ in atTop, ∀ k ∈ liveCarrierSet p,
      ((positiveFloorValues p k).card : ℝ) ≤ Real.log (p : ℝ)^2 := by
  filter_upwards [coefficient_cutoff_lower_eventually,eventually_ge_atTop (2 : ℕ)] with p hp hp2
  intro k hk
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hkstrip := (remaining_carrier_strip hk).1
  have hkR : 2*(coefficientSquareLockCutoff p : ℝ) < k := by exact_mod_cast hkstrip
  have hmul : (p : ℝ) ≤ (k+1 : ℕ)*Real.log (p : ℝ)^2 := by
    have hdiv : (p : ℝ)/Real.log p^2 ≤ ((k+1 : ℕ) : ℝ) := by push_cast; linarith
    exact (div_le_iff₀ (sq_pos_of_pos hl)).mp hdiv
  calc
    _ ≤ (((p-1)/(k+1) : ℕ) : ℝ) := by exact_mod_cast positiveFloorValues_card_le p k
    _ ≤ ((p-1 : ℕ) : ℝ)/((k+1 : ℕ) : ℝ) := Nat.cast_div_le
    _ ≤ (p : ℝ)/((k+1 : ℕ) : ℝ) := by gcongr; exact_mod_cast Nat.sub_le p 1
    _ ≤ Real.log (p : ℝ)^2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)

end NField.Alignment.SquareLockRemainingStrip
