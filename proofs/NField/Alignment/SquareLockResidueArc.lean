/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SquareLockCarrierMass

/-! # The exact centered-residue lock as a real short-arc condition -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockResidueArc
open SquareLockCarrierMass

theorem centered_residue_quotient (n k : ℕ) (hk : 0 < k) :
    ∃ z : ℤ, (n:ℝ)/(k:ℝ)-z = (centeredNaturalResidue n k:ℝ)/(k:ℝ) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdiv : ((n%k:ℕ):ℝ)+(k:ℝ)*((n/k:ℕ):ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n k
  unfold centeredNaturalResidue
  dsimp only
  split_ifs with h
  · refine ⟨((n/k:ℕ):ℤ),?_⟩
    simp only [Int.cast_natCast]
    field_simp
    linarith
  · refine ⟨((n/k:ℕ):ℤ)+1,?_⟩
    simp only [Int.cast_natCast,Int.cast_sub,Int.cast_add,Int.cast_one]
    field_simp
    linarith

theorem centered_residue_small_arc (n k C : ℕ) (hk : 0 < k)
    (hC : (centeredNaturalResidue n k).natAbs ≤ C) :
    ∃ z : ℤ, |(n:ℝ)/(k:ℝ)-z| ≤ (C:ℝ)/(k:ℝ) := by
  obtain ⟨z,hz⟩ := centered_residue_quotient n k hk
  refine ⟨z,?_⟩
  rw [hz,abs_div,abs_of_pos (show (0:ℝ)<k by exact_mod_cast hk)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  have hc : ((centeredNaturalResidue n k).natAbs:ℝ) ≤ C := by exact_mod_cast hC
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hc

end NField.Alignment.SquareLockResidueArc
