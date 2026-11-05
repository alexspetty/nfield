/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRestrictedEnergy

/-!
# A concrete terminal block at a fixed source offset

The terminal block is floor(log(log(x)))-B-2. All natural subtraction,
endpoint bounds and remaining-length comparisons are proved under an
explicit large-x condition. The offset is fixed before x and amplitude.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGoodEventCutoff
open HarperPrimeBlocks HarperFrequencyMesh HarperGoodAllowance

def terminalBlock (B : ℕ) (x : ℝ) : ℕ := ⌊Real.log (Real.log x)⌋₊-B-2

theorem terminalBlock_add {B : ℕ} {x : ℝ}
    (h : B+2 ≤ ⌊Real.log (Real.log x)⌋₊) :
    terminalBlock B x+B+2 = ⌊Real.log (Real.log x)⌋₊ := by
  unfold terminalBlock
  omega

theorem terminalLogScale_bounds {B : ℕ} {x : ℝ} (hx : 1 < x)
    (h : B+2 ≤ ⌊Real.log (Real.log x)⌋₊) :
    (B : ℝ)+1 ≤ terminalLogScale x (terminalBlock B x) ∧
      terminalLogScale x (terminalBlock B x) < (B : ℝ)+2 := by
  have hY : 1 ≤ Real.log (Real.log x) := (Nat.one_le_floor_iff _).mp (by omega)
  have hlo := Nat.floor_le (show 0 ≤ Real.log (Real.log x) by linarith)
  have hhi := Nat.lt_floor_add_one (Real.log (Real.log x))
  have he : (terminalBlock B x : ℝ)+B+2 = (⌊Real.log (Real.log x)⌋₊ : ℝ) := by
    exact_mod_cast terminalBlock_add h
  unfold terminalLogScale
  rw [log_logScale_eq hx]
  exact ⟨by linarith,by linarith⟩

theorem terminalBlock_large_condition {B : ℕ} {x : ℝ}
    (h : 2*((B : ℝ)+2) ≤ Real.log (Real.log x)) :
    B+2 ≤ ⌊Real.log (Real.log x)⌋₊ := by
  apply Nat.le_floor
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) B]

theorem terminalBlock_length {B : ℕ} {x : ℝ}
    (h : 2*((B : ℝ)+2) ≤ Real.log (Real.log x)) :
    Real.sqrt (Real.log (Real.log x)) ≤
      2*Real.sqrt ((terminalBlock B x+1 : ℕ) : ℝ) := by
  have hB := Nat.cast_nonneg (α := ℝ) B
  have hY : 0 ≤ Real.log (Real.log x) := by linarith
  have hfloor := Nat.lt_floor_add_one (Real.log (Real.log x))
  have he : (terminalBlock B x : ℝ)+B+2 = (⌊Real.log (Real.log x)⌋₊ : ℝ) := by
    exact_mod_cast terminalBlock_add (terminalBlock_large_condition h)
  have hlen : Real.log (Real.log x) ≤ 2*((terminalBlock B x+1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hs := Real.sq_sqrt hY
  have ht := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (terminalBlock B x+1))
  have hs0 := Real.sqrt_nonneg (Real.log (Real.log x))
  have ht0 := Real.sqrt_nonneg ((terminalBlock B x+1 : ℕ) : ℝ)
  nlinarith

theorem blockUpper_eq_double_exp {x : ℝ} (hx : 1 < x) (M : ℕ) :
    blockUpper x M = Real.exp (Real.exp (terminalLogScale x M)) := by
  simp only [terminalLogScale,logScale,Real.exp_log (Real.log_pos (blockUpper_gt_one hx M)),
    Real.exp_log (show 0 < blockUpper x M by linarith [blockUpper_gt_one hx M])]

theorem terminalBlock_threshold {B : ℕ} {X₀ x : ℝ} (hB : X₀ ≤ (B : ℝ)) (hx : 1 < x)
    (h : B+2 ≤ ⌊Real.log (Real.log x)⌋₊) : X₀ ≤ blockUpper x (terminalBlock B x) := by
  have hc := (terminalLogScale_bounds hx h).1
  have he := Real.add_one_le_exp (terminalLogScale x (terminalBlock B x))
  have hee := Real.add_one_le_exp (Real.exp (terminalLogScale x (terminalBlock B x)))
  rw [blockUpper_eq_double_exp hx]
  linarith

theorem terminal_pathAmplitude {B : ℕ} {x a : ℝ} (hx : 1 < x)
    (h : B+2 ≤ ⌊Real.log (Real.log x)⌋₊) (ha : 1 ≤ a) :
    pathAmplitude x (terminalBlock B x) a ≤ (3*(B : ℝ)+9)*a := by
  have hc := terminalLogScale_bounds hx h
  have hB := Nat.cast_nonneg (α := ℝ) B
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < terminalLogScale x (terminalBlock B x)+1 by linarith [hc.1])
  unfold pathAmplitude
  nlinarith [hc.2]

end NField.Alignment.HarperGoodEventCutoff
