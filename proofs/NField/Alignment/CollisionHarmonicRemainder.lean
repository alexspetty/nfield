/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLogQuadrature
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exact strict harmonic remainder

Two corrected harmonic sequences enclose the actual Euler-Mascheroni
constant. Their strict monotonicity gives the first neglected term with
the literal constant one twelfth at every positive natural argument.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicRemainder

open Filter CollisionLogQuadrature

def lowerSeq (n : ℕ) : ℝ := (harmonic n : ℝ)-Real.log (n+1)+1/(2*(n+1))
def upperSeq (n : ℕ) : ℝ := lowerSeq n+1/(12*(n+1)^2)

theorem log_successor_ratio (x : ℝ) (hx : 0<x) :
    Real.log (x+1)=Real.log x+Real.log (1+1/x) := by
  have hm : x*(1+1/x)=x+1 := by field_simp
  have hl := Real.log_mul hx.ne' (show 1+1/x≠0 by positivity)
  rw [hm] at hl
  exact hl

theorem lowerSeq_step (n : ℕ) :
    lowerSeq (n+1)-lowerSeq n=
      trapezoidLog (1/((n : ℝ)+1))-Real.log (1+1/((n : ℝ)+1)) := by
  have hx : 0<(n : ℝ)+1 := by positivity
  have he : 1/((n : ℝ)+1)+1/(2*((n : ℝ)+1+1))-1/(2*((n : ℝ)+1))=
      trapezoidLog (1/((n : ℝ)+1)) := by
    unfold trapezoidLog
    field_simp
    ring
  unfold lowerSeq
  rw [harmonic_succ]
  push_cast
  rw [log_successor_ratio _ hx]
  simp only [one_div] at he ⊢
  linarith

theorem upperSeq_step (n : ℕ) :
    upperSeq (n+1)-upperSeq n=
      trapezoidLog (1/((n : ℝ)+1))-Real.log (1+1/((n : ℝ)+1))-
        correctionLog (1/((n : ℝ)+1)) := by
  have hx : 0<(n : ℝ)+1 := by positivity
  have he : 1/(12*((n : ℝ)+1+1)^2)-1/(12*((n : ℝ)+1)^2)=
      -correctionLog (1/((n : ℝ)+1)) := by
    unfold correctionLog
    field_simp
    ring
  have hs := lowerSeq_step n
  unfold upperSeq
  push_cast
  linarith

theorem lowerSeq_strictMono : StrictMono lowerSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  have he := log_lt_trapezoid (by positivity : 0<1/((n : ℝ)+1))
  have hs := lowerSeq_step n
  linarith

theorem upperSeq_strictAnti : StrictAnti upperSeq := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have he := trapezoid_sub_correction_lt_log (by positivity : 0<1/((n : ℝ)+1))
  have hs := upperSeq_step n
  linarith

theorem reciprocal_succ_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (nhds 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have he := hi.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using he

theorem lowerSeq_tendsto : Tendsto lowerSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hs := Real.tendsto_harmonic_sub_log_add_one.add
    (reciprocal_succ_tendsto.const_mul (1/2 : ℝ))
  convert! hs using 1
  · funext n
    unfold lowerSeq
    field_simp
  · norm_num

theorem upperSeq_tendsto : Tendsto upperSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hs := lowerSeq_tendsto.add ((reciprocal_succ_tendsto.pow 2).const_mul (1/12 : ℝ))
  convert! hs using 1
  · funext n
    unfold upperSeq
    simp only [inv_pow]
    field_simp
  · norm_num

theorem lowerSeq_lt_gamma (n : ℕ) : lowerSeq n<Real.eulerMascheroniConstant :=
  (lowerSeq_strictMono (Nat.lt_succ_self n)).trans_le
    (lowerSeq_strictMono.monotone.ge_of_tendsto lowerSeq_tendsto (n+1))

theorem gamma_lt_upperSeq (n : ℕ) : Real.eulerMascheroniConstant<upperSeq n :=
  (upperSeq_strictAnti.antitone.le_of_tendsto upperSeq_tendsto (n+1)).trans_lt
    (upperSeq_strictAnti (Nat.lt_succ_self n))

def harmonicError (n : ℕ) : ℝ :=
  (harmonic (n-1) : ℝ)-Real.log n-Real.eulerMascheroniConstant+1/(2*n)

theorem harmonicError_bounds {n : ℕ} (hn : 1≤n) :
    -(1/(12*(n : ℝ)^2))<harmonicError n ∧ harmonicError n<0 := by
  have hl := lowerSeq_lt_gamma (n-1)
  have hu := gamma_lt_upperSeq (n-1)
  have hnR : (((n-1 : ℕ) : ℝ))+1=(n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hn
  simp only [upperSeq,lowerSeq,hnR] at hl hu
  unfold harmonicError
  constructor <;> linarith

theorem strict_harmonic_remainder {n : ℕ} (hn : 1≤n) :
    (harmonic (n-1) : ℝ)=Real.log n+Real.eulerMascheroniConstant-1/(2*n)+harmonicError n ∧
    -(1/(12*(n : ℝ)^2))<harmonicError n ∧ harmonicError n<0 := by
  refine ⟨?_,harmonicError_bounds hn⟩
  unfold harmonicError
  ring

end NField.Alignment.CollisionHarmonicRemainder
