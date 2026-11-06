/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CarrierStateSwitching

/-! # Exact counting meanings of the floor-state dwell weights -/
set_option autoImplicit false
namespace NField.Alignment.CarrierDwellCounts

theorem floor_state_interval {N X h : ℕ} (hX : 0<X) (hh : 0<h) :
    N/h=X ↔ N/(X+1)<h ∧ h ≤ N/X := by
  have he : N/h=X ↔ X ≤ N/h ∧ N/h<X+1 := by omega
  rw [he,Nat.le_div_iff_mul_le hh,Nat.div_lt_iff_lt_mul hh,
    Nat.div_lt_iff_lt_mul (Nat.succ_pos X),Nat.le_div_iff_mul_le hX]
  simp only [Nat.mul_comm,and_comm]

/-- Title: `A dwell difference counts exactly one floor state`. -/
theorem floor_state_count (N : ℕ) {X : ℕ} (hX : 0<X) :
    ((Finset.Icc 1 N).filter (fun h => N/h=X)).card=N/X-N/(X+1) := by
  have he : (Finset.Icc 1 N).filter (fun h => N/h=X)=Finset.Ioc (N/(X+1)) (N/X) := by
    ext h
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hh,hN⟩,hfloor⟩
      exact (floor_state_interval hX (by omega)).mp hfloor
    · intro hh
      have hpos : 0<h := (Nat.zero_le _).trans_lt hh.1
      exact ⟨⟨by omega,hh.2.trans (Nat.div_le_self N X)⟩,
        (floor_state_interval hX hpos).mpr hh⟩
  rw [he,Nat.card_Ioc]

/-- Title: `A lifetime weight counts every floor state at or above its cutoff`. -/
theorem floor_state_upper_count (N : ℕ) {X : ℕ} (hX : 0<X) :
    ((Finset.Icc 1 N).filter (fun h => X ≤ N/h)).card=N/X := by
  have he : (Finset.Icc 1 N).filter (fun h => X ≤ N/h)=Finset.Icc 1 (N/X) := by
    ext h
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hh,hN⟩,hfloor⟩
      refine ⟨hh,?_⟩
      rw [Nat.le_div_iff_mul_le hX]
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0<h)).mp hfloor
    · intro hh
      refine ⟨⟨hh.1,hh.2.trans (Nat.div_le_self N X)⟩,?_⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0<h)]
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hX).mp hh.2
  rw [he,Nat.card_Icc]
  simp

end NField.Alignment.CarrierDwellCounts
