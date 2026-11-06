/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SmoothingFiniteFrequency
import NField.Alignment.ReciprocalFloorSmoothing

/-! # A uniform reciprocal sawtooth block from the exact smoothing formula -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSmoothedBlock
open scoped BigOperators Classical
open ReciprocalWeightedBlocks ReciprocalSawtoothSmoothing ReciprocalFloorSmoothing
  SmoothingFiniteFrequency

theorem phase_reciprocal (n k : ℕ) (Q : ℝ) :
    phase (n : ℤ) (Q/(k : ℝ))=reciprocalPhase ((n : ℝ)*Q) k := by
  unfold phase reciprocalPhase
  rw [fourier_coe_apply]
  push_cast
  congr 1
  ring

theorem smoothed_block_bound (p M H : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hH : 1 ≤ H) (hPQ : (p : ℝ)^2 ≤ Q) :
    |smoothedPrefix p M Q (1/(H : ℝ))| ≤
      48*Real.sqrt (Q/(p : ℝ))*Real.sqrt (H : ℝ)+
      128*Real.sqrt ((p : ℝ)*(1+Real.log p))*((harmonic H : ℝ)+1) := by
  have h := smoothed_finite_frequency_bound (Finset.range M)
    (fun i => Q/((p+i+1 : ℕ) : ℝ)) hH
    (A := 6*Real.sqrt (Q/(p : ℝ))) (B := 64*Real.sqrt ((p : ℝ)*(1+Real.log p)))
    (by positivity) (by positivity) (fun n hn => by
      simp_rw [phase_reciprocal]
      exact reciprocal_frequency_root_bound p M n Q hp hM hn hPQ)
  unfold smoothedPrefix
  convert h using 1 <;> ring

/-- A block estimate with every smoothing constraint stated explicitly. -/
theorem floor_block_bound_with_cutoff (p M H : ℕ) (X T : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hH : 2 ≤ H) (hpX : (p : ℝ) ≤ X)
    (hHT : (p : ℝ)/(H : ℝ) ≤ T) (hT : 0 < T)
    (hX : X^2 ≤ T^3) (hlog : (p : ℝ)*(1+Real.log p) ≤ 4*T^2)
    (hfreq : X^2/(p : ℝ)*(H : ℝ) ≤ 4*T^2)
    (hlogmass : (p : ℝ)*(1+Real.log p)*((harmonic H : ℝ)+1)^2 ≤ T^2) :
    |floorSawPrefix p M (X^2)| ≤ 1400*T := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp
  have hX0 : 0 < X := hp0.trans_le hpX
  have hPQ : (p : ℝ)^2 ≤ X^2 := by nlinarith
  have herr := floor_block_smoothing_error p M H X T hp hM hH hpX hHT hT hX hlog
  have hsm := smoothed_block_bound p M H (X^2) hp hM (by omega) hPQ
  have hroot1 : (Real.sqrt (X^2/(p : ℝ))*Real.sqrt (H : ℝ))^2 =
      X^2/(p : ℝ)*(H : ℝ) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (Nat.cast_nonneg H)]
  have hroot2 : (Real.sqrt ((p : ℝ)*(1+Real.log p))*((harmonic H : ℝ)+1))^2 =
      (p : ℝ)*(1+Real.log p)*((harmonic H : ℝ)+1)^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hh : 0 ≤ (harmonic H : ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have h1 : Real.sqrt (X^2/(p : ℝ))*Real.sqrt (H : ℝ) ≤ 2*T := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (X^2/(p : ℝ))) (Real.sqrt_nonneg (H : ℝ))]
  have h2 : Real.sqrt ((p : ℝ)*(1+Real.log p))*((harmonic H : ℝ)+1) ≤ T := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg ((p : ℝ)*(1+Real.log p))) (by linarith : 0 ≤ (harmonic H : ℝ)+1)]
  have htri := abs_add_le (floorSawPrefix p M (X^2)-smoothedPrefix p M (X^2) (1/(H : ℝ)))
    (smoothedPrefix p M (X^2) (1/(H : ℝ)))
  rw [sub_add_cancel] at htri
  nlinarith

end NField.Alignment.ReciprocalSmoothedBlock
