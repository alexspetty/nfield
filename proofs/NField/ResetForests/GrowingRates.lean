/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Growing
/-! # Growing-window work in the original sampling units

The finite initial segment is absorbed into a genuine uniform constant.
The growing-window divisor estimate supplies the subpower factor rather
than appearing as an unproved assumption in the final theorem.
-/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open scoped BigOperators Topology
open Filter NField.Alignment AbsoluteForestWork SignedForestWork
open DedekindFourierMoment

theorem uniform_power_bound_of_eventually (f : ℕ → ℝ) (a C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ C*(n : ℝ)^a) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → f n ≤ B*(n : ℝ)^a := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  let B := C+∑ n ∈ Finset.Icc 1 M, |f n|/(n : ℝ)^a
  have hs : 0 ≤ ∑ n ∈ Finset.Icc 1 M, |f n|/(n : ℝ)^a :=
    Finset.sum_nonneg (fun n _ => by positivity)
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ)^a := Real.rpow_pos_of_pos hnR _
  by_cases hlarge : M ≤ n
  · exact (hM n hlarge).trans
      (mul_le_mul_of_nonneg_right (show C ≤ B by dsimp [B]; linarith) hpow.le)
  · have hmem : n ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hn, by omega⟩
    have hterm := Finset.single_le_sum (f := fun n : ℕ => |f n|/(n : ℝ)^a)
      (fun n _ => by positivity) hmem
    have hquot : f n/(n : ℝ)^a ≤ B :=
      (div_le_div_of_nonneg_right (le_abs_self _) hpow.le).trans
        (hterm.trans (by dsimp [B]; linarith))
    exact (div_le_iff₀ hpow).mp hquot

theorem growing_triple_divisor_uniform {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p →
      (Core.tripleDivisorCount (returnDivisor p (L p)) : ℝ) ≤ C*(p : ℝ)^ε :=
  uniform_power_bound_of_eventually _ ε 1 (by norm_num)
    (by simpa only [one_mul] using growing_triple_divisor_subpower hL ε hε)

theorem growing_window_absolute {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      Core.absoluteForestReading (p-1) (p^2) (returnDivisor p (L p)) ≤
        C*(p : ℝ)^(3/2+ε) := by
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, ha⟩ := whole_forest_absolute_bound δ hδ
  obtain ⟨B, hB, hb⟩ := growing_triple_divisor_uniform hL δ hδ
  let H : ℝ := 1+1/δ
  refine ⟨A/2*H*B, by dsimp [H]; positivity, ?_⟩
  intro p hp hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : 0 < p-1 := by omega
  have hH0 : (0 : ℝ) ≤ (harmonic (p-1) : ℝ) := by
    simpa using harmonic_cast_mono (Nat.zero_le (p-1))
  have hHN : (harmonic (p-1) : ℝ) ≤ H*(p : ℝ)^δ :=
    (harmonic_cast_mono (Nat.sub_le p 1)).trans
      (PhasePopulations.harmonic_small_power_from_mathlib δ hδ hp.one_le)
  have hpower : (((p-1 : ℕ) : ℝ))^(3/2+2*δ) ≤ (p : ℝ)^(3/2+2*δ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) (by positivity)
  calc
    _ ≤ (A/2)*(((p-1 : ℕ) : ℝ))^(3/2+2*δ)*
        (harmonic (p-1) : ℝ)*(Core.tripleDivisorCount (returnDivisor p (L p)) : ℝ) :=
      ha _ _ _ hN (return_divisor_pos hp3 _)
    _ ≤ (A/2)*(p : ℝ)^(3/2+2*δ)*(H*(p : ℝ)^δ)*(B*(p : ℝ)^δ) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (by positivity)) hHN hH0 (by positivity)
      · exact hb p hp.one_le
      · positivity
      · positivity
    _ = (A/2*H*B)*(((p : ℝ)^(3/2+2*δ)*(p : ℝ)^δ)*(p : ℝ)^δ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hpR, ← Real.rpow_add hpR]
      congr 2
      dsimp [δ]
      ring

theorem growing_window_sampling {L : ℕ → ℕ} (hL : GrowingReturnWindow L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) (returnDivisor p (L p)))/(p : ℝ)^2| ≤
        C*(p : ℝ)^(-1/2+ε) := by
  obtain ⟨C, hC, hc⟩ := growing_window_absolute hL ε hε
  refine ⟨4*C, by positivity, ?_⟩
  intro p hp hodd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    _ = 4*|Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) (returnDivisor p (L p)))|/(p : ℝ)^2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (p : ℝ))]
      norm_num
    _ ≤ 4*Core.absoluteForestReading (p-1) (p^2) (returnDivisor p (L p))/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (selected_forest_abs_le _ _ _) (by norm_num)) (sq_nonneg _)
    _ ≤ 4*(C*(p : ℝ)^(3/2+ε))/(p : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc p hp hodd) (by norm_num)) (sq_nonneg _)
    _ = _ := by
      rw [show 4*(C*(p : ℝ)^(3/2+ε))/(p : ℝ)^2=(4*C)*((p : ℝ)^(3/2+ε)/(p : ℝ)^2) by ring,
        ← Real.rpow_two, ← Real.rpow_sub hpR, show (3/2+ε : ℝ)-2=-1/2+ε by ring]

end NField.ResetForests.ReturnWindows
